template = src/template.rs
macro = src/macro.rs

.PHONY: test valgrind miri clean

$(macro): generate_macro.zsh $(template)
	zsh $< $(template) $@

test: $(macro)
	cargo test

valgrind: $(macro)
	cargo valgrind test

miri: $(macro)
	cargo +nightly miri test

clean:
	cargo clean && rm -rf $(macro)
