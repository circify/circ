./src/macro_.rs: ./src/template.rs ./generate_macro.zsh
	zsh ./generate_macro.zsh ./src/template.rs $@

test:
	cargo test

valgrind:
	cargo valgrind test

miri:
	cargo +nightly miri test

