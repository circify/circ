template = src/template.rs
u8 = src/hc_u8.rs
macro = src/macro_.rs

.PHONY: test valgrind miri clean all

generated = $(macro) $(u8)

all: $(generated)

$(macro): generate_macro.zsh $(template)
	zsh $< $(template) $@

$(u8): generate_u8.zsh $(template)
	zsh $< $(template) $@

test: $(generated)
	cargo test

valgrind: $(generated)
	cargo valgrind test

miri: $(generated)
	cargo +nightly miri test

clean:
	cargo clean && rm -rf $(generated)
