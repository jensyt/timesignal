//! Defines a very basic allocator.
//!
//! For non-WASM targets, this uses the Rust standard library allocator. For WASM targets, it uses
//! a simple singly-linked list of memory allocations starting at `__heap_size` as defined by LLD.
//! It does not request additional memory from the WASM runtime, so using more memory than is
//! configured at program start will result in an allocation failure and immediate termination of
//! the program.
//!
//! # Examples
//!
//! ```
//! let layout = Layout::new::<u32>();
//! unsafe {
//! 	let ptr = alloc(layout);
//! 	// ptr is guaranteed to be non-null and aligned.
//! 	ptr.write(42);
//! }
//! ```

/// WASM memory allocator implementation.
///
/// This allocator uses a simple singly-linked list of memory allocations with a fixed maximum
/// memory size set by the WASM runtime at startup. Allocations that would exceed the maximum
/// will result in immediately halting the program.
///
/// Each allocated memory block is laid out with a block header immediately followed by the block
/// data. If the required alignment for the block data is greater than for the block header,
/// padding is added *before* the block header rather than between the block header and block data.
///
/// This strategy has several implications:
/// - Each memory allocation has at least `BLOCK_LAYOUT.size()` bytes of overhead.
/// - No two memory allocations will have contiguous block data.
/// - Each memory allocation is `O(n)` where `n` is the number of active allocations.
///
/// # Why?
///
/// This simple allocator is small (~600 bytes of binary WASM pre-gzip) and the time signal
/// application makes relatively few allocations, so performance is not critical. Even simpler
/// strategies typically do not handle dealloc, which could lead to unecessary failures if
/// users start and stop time signal generation repeatedly.
#[cfg(target_arch = "wasm32")]
mod impl_wasm {
	use core::cell::UnsafeCell;
	use core::alloc::Layout;
	use core::arch::wasm32;
	use core::ptr;

	/// The size of a WebAssembly page in bytes.
	const PAGE_SIZE: usize = 65536;

	unsafe extern "C" {
		/// The base address of the heap, set by the linker.
		///
		/// The *value* is meaningless and should not be read. Linker symbols store their value in the
		/// address of the symbol, rather than in the location pointed to by the address. See the
		/// [ld documentation] for more details.
		///
		/// # Examples
		/// ```
		/// let heap_base = &raw const __heap_base;
		/// ```
		///
		/// [ld documentation]: https://sourceware.org/binutils/docs/ld/Source-Code-Reference.html
		static __heap_base: u8;
	}

	/// Get the base address of the heap, accounting for the custom argument stack size.
	#[inline(always)]
	fn heap_base() -> usize {
		&raw const __heap_base as usize + crate::CUSTOM_STACK_SIZE
	}

	/// Handle allocation errors by halting execution.
	#[inline(always)]
	fn handle_alloc_error() -> ! {
		wasm32::unreachable()
	}

	/// A header for a block of allocated memory.
	struct Block {
		/// The next allocated block, or null if no more blocks.
		next: *mut Block,
		/// The size of this memory block, excluding this header.
		size: usize
	}

	/// Layout details for a block header.
	const BLOCK_LAYOUT: Layout = Layout::new::<Block>();

	/// Global allocator state.
	///
	/// There should only ever be one active allocator, since it manages the entire heap.
	struct Allocator {
		/// The head of the allocated blocks linked list. This must be set to an empty block header.
		head: UnsafeCell<*mut Block>,
		/// The total size of the WASM linear memory in bytes. The available size of the heap for
		/// dynamic memory allocation is approximately `size - heap_base()`.
		size: UnsafeCell<usize>
	}

	impl Allocator {
		/// Construct a new [`Allocator`] instance.
		///
		/// This function initializes the allocator with an empty head block and retrieves the total
		/// size of WASM linear memory.
		fn new() -> Self {
			let head = next_offset(heap_base(), BLOCK_LAYOUT.align());
			let size = wasm32::memory_size(0) * PAGE_SIZE;
			if head + BLOCK_LAYOUT.size() >= size {
				handle_alloc_error();
			}

			let head = head as *mut Block;
			// Safety: head is appropriately aligned and large enough to hold a block header.
			unsafe { head.write(Block { next: ptr::null_mut(), size: 0 }); }

			Allocator {
				size: UnsafeCell::new(size),
				head: UnsafeCell::new(head)
			}
		}

		/// Get the head block and total size of the allocator.
		///
		/// If the allocator is empty, it will be initialized via [`Allocator::new`].
		fn get(&self) -> (*mut Block, usize) {
			let head = self.head.get();
			let size = self.size.get();
			// Safety: this allocator only runs in single-threaded environments, so it is safe to
			// initialize the allocator during this call. All pointers are guaranteed to be valid.
			unsafe {
				if *size == 0 {
					let new = Allocator::new();
					head.write(*new.head.get());
					size.write(*new.size.get());
				}
				(*head, *size)
			}
		}
	}

	/// This allocator is safe to use in a single-threaded WASM environment only. Implements [`Sync`]
	/// to enable the static global [`ALLOCATOR`].
	unsafe impl Sync for Allocator {}

	/// Global allocator.
	static ALLOCATOR: Allocator = Allocator {
		head: UnsafeCell::new(ptr::null_mut()),
		size: UnsafeCell::new(0)
	};

	/// Compute the next offset for a given starting offset and alignment.
	///
	/// If `offset` is already aligned to `align`, it is returned as is.
	#[inline(always)]
	fn next_offset(offset: usize, align: usize) -> usize {
		(offset + align - 1) & align.wrapping_neg()
	}

	/// Allocate a block of memory with a given layout.
	///
	/// The returned pointer is to the block data (not the block header) and can be used directly by
	/// the caller.
	///
	/// # Safety
	///
	/// This function must only be called from a single thread.
	///
	/// # Panics
	///
	/// This function halts execution if the allocation would overflow the available memory.
	pub unsafe fn alloc(layout: Layout) -> *mut u8 {
		let (joint_layout, data_offset) = match BLOCK_LAYOUT.extend(layout) {
			Ok(v) => v,
			Err(_) => handle_alloc_error()
		};

		let (mut blocks, max_size) = ALLOCATOR.get();

		loop {
			// Safety: ALLOCATOR always has at least one empty block header, and we perform a null check
			// at the end of each loop iteration to make sure this pointer is valid
			let block = unsafe { &mut *blocks };

			let mut offset = next_offset(
				blocks as usize + BLOCK_LAYOUT.size() + block.size,
				joint_layout.align()
			);
			let end_offset = offset + joint_layout.size();

			// Ensure we do not attempt to allocate more memory than is available
			if end_offset >= max_size {
				handle_alloc_error();
			}

			// Check if there is enough space after the current block and before the next one
			if block.next.is_null() || end_offset < block.next as usize {
				// Adjust block header to be left-padded rather than right-padded. This ensures that the
				// block data immediately follows the block header.
				if data_offset > BLOCK_LAYOUT.size() {
					offset += data_offset - BLOCK_LAYOUT.size();
				}

				// Insert the new block
				let next = block.next;
				block.next = offset as *mut Block;
				blocks = block.next;
				unsafe {
					blocks.write(Block { next, size: layout.size() });

					// Return a pointer to the block data
					return blocks.add(1) as *mut u8;
				}
			}

			blocks = block.next;
		}
	}

	/// Deallocates a block of memory previously allocated by [`alloc`].
	///
	/// # Safety
	///
	/// This function must only be called from a single thread.
	///
	/// # Panics
	///
	/// If the memory was not allocated by [`alloc`], was previously deallocated, or was allocated
	/// with a different layout, this function immediately halts the program.
	pub unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
		let (mut blocks, _) = ALLOCATOR.get();

		unsafe { loop {
			let prior = blocks;
			// Safety: ALLOCATOR always has at least one empty block header, and we perform a null check
			// below to make sure blocks is never null at the start of this loop.
			blocks = (*blocks).next;

			if blocks.is_null() {
				// Tried to dealloc an invalid pointer
				handle_alloc_error();
			}

			let block_ptr = blocks.add(1) as *mut u8;
			if ptr == block_ptr {
				if (*blocks).size != layout.size() {
					// Tried to dealloc an invalid pointer
					handle_alloc_error();
				}
				(*prior).next = (*blocks).next;
				return;
			}
		}}
	}

	#[cfg(test)]
	mod tests {
		use super::*;

		#[test]
		fn next_offset_test() {
			assert_eq!(next_offset(0, 2), 0);
			assert_eq!(next_offset(0, 4), 0);
			assert_eq!(next_offset(0, 8), 0);
			assert_eq!(next_offset(1, 2), 2);
			assert_eq!(next_offset(1, 4), 4);
			assert_eq!(next_offset(1, 8), 8);
			assert_eq!(next_offset(62165, 2), 62166);
			assert_eq!(next_offset(62165, 4), 62168);
			assert_eq!(next_offset(62165, 8), 62168);
		}

		fn get_allocator_test() {
			let (blocks, size) = ALLOCATOR.get();
			assert!(size > 0);
			assert!(!blocks.is_null());
			unsafe {
				assert!((*blocks).next.is_null());
				assert_eq!((*blocks).size, 0);
			}
		}

		#[test]
		fn simple_alloc_test() {
			get_allocator_test();

			unsafe {
				let layout = Layout::new::<u32>();
				let ptr = alloc(layout);
				assert!(!ptr.is_null());
				let (blocks, _) = ALLOCATOR.get();
				assert!(!(*blocks).next.is_null());
				assert_eq!((*blocks).size, 0);
				assert_eq!((*blocks).next, blocks.add(1));
				let blocks = (*blocks).next;
				assert!((*blocks).next.is_null());
				assert_eq!((*blocks).size, layout.size());

				dealloc(ptr, layout);
			}

			get_allocator_test();
		}

		#[test]
		fn multi_alloc_test() {
			get_allocator_test();

			unsafe {
				let layout1 = Layout::new::<u32>();
				let ptr1 = alloc(layout1);
				assert!(!ptr1.is_null());
				let (blocks, _) = ALLOCATOR.get();
				assert_eq!((*blocks).next, blocks.add(1));
				assert_eq!((*blocks).size, 0);
				let blocks = (*blocks).next;
				assert!((*blocks).next.is_null());
				assert_eq!((*blocks).size, layout1.size());

				let layout2 = Layout::new::<u64>();
				let ptr2 = alloc(layout2);
				assert!(!ptr2.is_null());
				let loc = next_offset(blocks.add(1).byte_add(layout1.size()) as usize, layout2.align()) as *mut Block;
				assert_eq!((*blocks).next, loc);
				let blocks = (*blocks).next;
				assert!((*blocks).next.is_null());
				assert_eq!((*blocks).size, layout2.size());

				dealloc(ptr1, layout1);

				let (blocks, _) = ALLOCATOR.get();
				assert_eq!((*blocks).next, loc);

				let ptr3 = alloc(layout2);
				assert!(!ptr3.is_null());
				assert_eq!((*blocks).next, loc);
				let blocks = (*blocks).next;
				assert_eq!((*blocks).next, loc.add(1).byte_add(layout2.size()));
				let blocks = (*blocks).next;
				assert_eq!((*blocks).size, layout2.size());

				let ptr4 = alloc(layout1);
				assert_eq!(ptr1, ptr4);
				let (blocks, _) = ALLOCATOR.get();
				assert_eq!((*blocks).next, blocks.add(1));
				let blocks = (*blocks).next;
				assert_eq!((*blocks).next, loc);

				dealloc(ptr3, layout2);
				assert!((*(*blocks).next).next.is_null());

				dealloc(ptr2, layout2);
				assert!((*blocks).next.is_null());

				dealloc(ptr1, layout1);
			}

			get_allocator_test();
		}
	}
}

/// Non-WASM memory allocator implementation.
///
/// This simply uses the standard library's allocator, with one nuance: if memory allocation fails,
/// the allocator calls [`handle_alloc_error`](alloc::alloc::handle_alloc_error) which immediately
/// halts execution.
#[cfg(not(target_arch = "wasm32"))]
mod impl_std {
	extern crate alloc;
	use core::alloc::Layout;

	/// Allocate a block of memory with the given layout.
	///
	/// See [`alloc`](alloc::alloc::alloc) for more details. Unlike the standard library's `alloc`,
	/// this function never returns a null pointer. It halts execution instead.
	pub unsafe fn alloc(layout: Layout) -> *mut u8 {
		use alloc::alloc::{alloc, handle_alloc_error};

		let ptr = unsafe { alloc(layout) };
		if ptr.is_null() {
			handle_alloc_error(layout)
		}
		ptr
	}

	/// Deallocate a block of memory with the given layout.
	///
	/// See [`dealloc`](alloc::alloc::dealloc) for more details.
	pub unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
		unsafe { alloc::alloc::dealloc(ptr, layout) }
	}
}

#[cfg(target_arch = "wasm32")]
pub use impl_wasm::*;
#[cfg(not(target_arch = "wasm32"))]
pub use impl_std::*;
