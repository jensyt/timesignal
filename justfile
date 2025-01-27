default: test

test:
	cargo test -p time --all-targets
	cargo test -p time --features now --all-targets
	cargo test -p time --features alloc --all-targets
	cargo test -p time --features std --all-targets
	cargo test -p signals --all-targets
	cargo test -p sntp --all-targets
	cargo test --all-features --all-targets

doctest:
	cargo test --workspace --all-features --doc

doc:
	cargo +nightly rustdoc --all-features -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links
	cargo +nightly rustdoc --all-features -p time  -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links
	cargo +nightly rustdoc --all-features -p sntp  -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links
	cargo +nightly rustdoc --all-features -p signals  -- --cfg docsrs --document-private-items -A rustdoc::private-intra-doc-links
