// Encode an ASCII string from 16-bit to 8-bit (JS-WASM interop)
function encodeAscii(dst, str) {
	const length = str.length < dst.length ? str.length : dst.length;
	for (let i = 0; i < length; i++) {
		dst[i] = str.charCodeAt(i) & 0x7F;
	}
	return length;
}

// Decode an ASCII string from 8-bit to 16-bit (JS-WASM interop)
function decodeAscii(bytes) {
	return Array.from(bytes, (byte) => String.fromCharCode(byte & 0x7F)).join('');
}

// Wrapper around our WebAssembly module. This MUST stay in sync with changes to lib/web/src/lib.rs.
// This wapper (and the underlying WASM) are not thread safe! They should only be used from a single
// thread!
class TimeSignal {
	// Supported signal types
	static JUNGHANS = 0;
	static WWVB = 1;
	static DCF77 = 2;

	// WASM parameter stack size
	static #STACK_SIZE = 1024;
	// WASM maximum error string length
	static #MAX_ERROR_LEN = 64;

	constructor(instance) {
		this.instance = instance;
	}

	// Get the parameter stack as a Uint8Array
	get_stack_as_uint8array() {
		return new Uint8Array(this.instance.exports.memory.buffer)
			.subarray(
				this.instance.exports.__heap_base.value,
				this.instance.exports.__heap_base.value + TimeSignal.#STACK_SIZE
			);
	}

	// Get the parameter stack as a DataView
	get_stack_as_dataview() {
		return new DataView(this.instance.exports.memory.buffer,
			this.instance.exports.__heap_base.value, TimeSignal.#STACK_SIZE);
	}

	// Make a writer for the given signal and timezone. An empty timezone string uses the default for
	// the signal. The writer is made to transmit the current time (`Date.now()`).
	// On success, returns a `Writer`. On failure, returns an error string.
	make_writer(signal, timezone) {
		const data = this.get_stack_as_uint8array();
		const len = encodeAscii(data, timezone);
		const handle = this.instance.exports.make_writer(
			signal, // Signal type
			BigInt(Date.now()), // Current time
			data.byteOffset, // Where we wrote the timezone string
			len // Length of the timezone string
		);
		return handle == 0 ? this.read_error() : new Writer(this, handle);
	}

	// Read an error string from the stack. This function should only be called if one of the WASM
	// functions returns 0.
	read_error() {
		const data = this.get_stack_as_uint8array();
		const end = data.findIndex((v, i) => v == 0 || i > TimeSignal.#MAX_ERROR_LEN);
		return decodeAscii(data.subarray(0, end));
	}
}

// Wrapper around a WASM writer. Note that failure to call `destroy` will result in a memory leak
// in the WebAssembly module.
class Writer {
	constructor(parent, handle) {
		this.parent = parent;
		this.handle = handle;
	}

	destroy() {
		this.parent.instance.exports.destroy_writer(this.handle);
	}

	// Write the encoded time signal to `buffer`. On success, returns the number of values written
	// to buffer, which may be less than `buffer.length`. On failure, returns an error string.
	write(buffer) {
		const dv = this.parent.get_stack_as_dataview();
		// Floats a 4 bytes
		const length = buffer.length <= dv.byteLength / 4 ? buffer.length : dv.byteLength / 4;

		const status = this.parent.instance.exports.write_signal(
			this.handle,
			dv.byteOffset, // Where to write the values
			length // Number of values to write
		);

		if (status > 0) {
			for (let i = 0; i < length; i++) {
				buffer[i] = dv.getFloat32(i * 4, true);
			}
			return length;
		} else {
			return this.parent.read_error();
		}
	}
}

class WorkletProcessor extends AudioWorkletProcessor {
	constructor(options) {
		super(options);
		this.port.onmessage = (event) => this.onMessage(event.data);
	}

	onMessage(event) {
		switch (event.type) {
			case 'init':
				this.wasm = WebAssembly.instantiate(event.module);
				break;
			case 'play':
				delete this.writer;
				const f = (instance) => {
					// Wrap the WebAssembly module
					if (!(instance instanceof TimeSignal)) {
						this.timesignal = new TimeSignal(instance);
					}

					let signal = TimeSignal.JUNGHANS;
					switch (event.signal) {
						case 'wwvb':
							signal = TimeSignal.WWVB;
							break;
						case 'dcf77':
							signal = TimeSignal.DCF77;
							break;
					}

					// Make a writer or report an error
					const writer = this.timesignal.make_writer(signal, event.timezone);
					if (writer instanceof Writer) {
						this.writer = writer;
					} else {
						console.error(`Failed to create writer: "${writer}"`);
						this.port.postMessage({ type: "error", message: `Failed to create writer: "${writer}"` });
					}
				};
				if (this.timesignal) {
					f(this.timesignal);
				} else {
					this.wasm.then(f);
				}
				break;
			case 'stop':
				// Clean up
				if (this.writer) {
					this.writer.destroy();
					delete this.writer;
				}
				break;
			default:
				console.error("Unknown message type");
				this.port.postMessage({ type: "error", message: "Unknown message type" });
		}
	}

	process(inputs, outputs, parameters) {
		if (this.writer) {
			// Generate the signal
			const status = this.writer.write(outputs[0][0]);
			if (typeof status !== 'string') {
				// Copy to other outputs and channels if needed
				for (let i = 0; i < outputs.length; i++) {
					const output = outputs[i];
					for (let j = i == 0 ? 1 : 0; j < output.length; j++) {
						const channel = output[j];
						for (let k = 0; k < channel.length; k++) {
							channel[k] = outputs[0][0][k];
						}
					}
				}
			} else {
				console.error(`Failed to write audio: "${status}"`);
				this.port.postMessage({ type: "error", message: `Failed to write audio: "${status}"` });
				return false;
			}
		} else {
			// Output silence if not ready or an error occurred
			for (let i = 0; i < outputs.length; i++) {
				const output = outputs[i];
				for (let j = 0; j < output.length; j++) {
					const channel = output[j];
					for (let k = 0; k < channel.length; k++) {
						channel[k] = 0;
					}
				}
			}
		}
		return true;
	}
}

registerProcessor('worklet-processor', WorkletProcessor);
