raw_template = src/raw/template.rs
raw_u8 = src/raw/example_u8.rs
raw_macro = src/raw/macro_.rs
raw_gen = $(raw_macro) $(raw_u8)
hashconsing_template = src/hashconsing/template.rs
hashconsing_u8 = src/hashconsing/example_u8.rs
hashconsing_macro = src/hashconsing/macro_.rs
hashconsing_gen = $(hashconsing_macro) $(hashconsing_u8)
rc_template = src/rc/template.rs
rc_u8 = src/rc/example_u8.rs
rc_macro = src/rc/macro_.rs
rc_gen = $(rc_macro) $(rc_u8)

.PHONY: test valgrind miri clean all

generated = $(raw_gen) $(hashconsing_gen) $(rc_gen)

all: $(generated)

$(raw_macro): generate_macro.zsh $(raw_template)
	zsh $< $(raw_template) $@ generate_hashcons_raw

$(raw_u8): generate_u8.zsh $(raw_template)
	zsh $< $(raw_template) $@

$(hashconsing_macro): generate_macro.zsh $(hashconsing_template)
	zsh $< $(hashconsing_template) $@ generate_hashcons_hashconsing

$(hashconsing_u8): generate_u8.zsh $(hashconsing_template)
	zsh $< $(hashconsing_template) $@

$(rc_macro): generate_macro.zsh $(rc_template)
	zsh $< $(rc_template) $@ generate_hashcons_rc

$(rc_u8): generate_u8.zsh $(rc_template)
	zsh $< $(rc_template) $@

test: $(generated)
	cargo test

valgrind: $(generated)
	cargo valgrind test

miri: $(generated)
	cargo +nightly miri test

clean:
	cargo clean && rm -rf $(generated)
