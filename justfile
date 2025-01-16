default: test

test:
	cargo test -p time --all-targets
	cargo test -p time --features now --all-targets
	cargo test -p time --features alloc --all-targets
	cargo test -p time --features std --all-targets
	cargo test --workspace --all-features --all-targets

doctest:
	cargo test --workspace --all-features --doc

doc:
	cargo +nightly rustdoc --all-features -- --cfg docsrs --document-private-items
	cargo +nightly rustdoc --all-features -p time  -- --cfg docsrs --document-private-items
	cargo +nightly rustdoc --all-features -p sntp  -- --cfg docsrs --document-private-items
