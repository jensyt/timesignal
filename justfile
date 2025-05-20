default: test

test:
	cargo test -p time --all-targets
	cargo test -p time --features now --all-targets
	cargo test -p time --features alloc --all-targets
	cargo test -p time --features std --all-targets
	cargo test -p signals --all-targets
	cargo test -p sntp --all-targets
	cargo test -p timesignal --all-features --all-targets

doctest:
	cargo test --workspace --all-features --doc

doc:
	cargo +nightly rustdoc --all-features -p timesignal -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links
	cargo +nightly rustdoc --all-features -p time  -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links
	cargo +nightly rustdoc --all-features -p sntp  -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links
	cargo +nightly rustdoc --all-features -p signals  -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links

build:
	RUSTFLAGS="-Zlocation-detail=none -Zfmt-debug=none" cargo +nightly build --release -Z build-std=std,panic_abort -Z build-std-features=panic_immediate_abort

wasm:
	cargo build -r -p web --target wasm32-unknown-unknown
	wasm-opt --enable-simd -o target/wasm32-unknown-unknown/release/web.opt.wasm -Oz target/wasm32-unknown-unknown/release/web.wasm
	cp target/wasm32-unknown-unknown/release/web.opt.wasm lib/web/html-js/web.wasm

wasmtest:
	cargo test -p web --target wasm32-wasip2

wasmdoc:
	cargo rustdoc --target=wasm32-unknown-unknown -p time  -- --document-private-items -A rustdoc::private-intra-doc-links
	cargo rustdoc --target=wasm32-unknown-unknown -p signals  -- --document-private-items -A rustdoc::private-intra-doc-links
	cargo rustdoc --target=wasm32-unknown-unknown -p web -- --document-private-items -A rustdoc::private-intra-doc-links
