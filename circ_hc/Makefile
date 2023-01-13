raw_template = src/raw/template.rs
raw_u8 = src/raw/example_u8.rs
raw_macro = src/raw/macro_.rs

.PHONY: test valgrind miri clean all

generated = $(raw_macro) $(raw_u8)

all: $(generated)

$(raw_macro): generate_macro.zsh $(raw_template)
	zsh $< $(raw_template) $@

$(raw_u8): generate_u8.zsh $(raw_template)
	zsh $< $(raw_template) $@

test: $(generated)
	cargo test

valgrind: $(generated)
	cargo valgrind test

miri: $(generated)
	cargo +nightly miri test

clean:
	cargo clean && rm -rf $(generated)
