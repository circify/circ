all: build test 

build: init
	cargo build --release --example circ && ./scripts/build_mpc_zokrates_test.zsh && ./scripts/build_aby.zsh

test:
	cargo test && ./scripts/zokrates_test.zsh && python3 ./scripts/test_aby.py && ./scripts/test_zok_to_ilp.zsh && ./scripts/test_zok_to_ilp_pf.zsh && ./scripts/test_datalog.zsh

init:
	git submodule update --init

aby:
	./scripts/build_mpc_zokrates_test.zsh && ./scripts/build_aby.zsh && python3 ./scripts/test_aby.py

clean:
	# remove all generated files
	touch ./third_party/ABY/build && rm -r -- ./third_party/ABY/build 
	touch ./third_party/ABY/src/examples/2pc_* && rm -r -- ./third_party/ABY/src/examples/2pc_* 
	sed '/add_subdirectory.*2pc.*/d' -i ./third_party/ABY/src/examples/CMakeLists.txt 
	rm -rf P V pi perf.data perf.data.old flamegraph.svg

format:
	cargo fmt --all

lint:
	cargo clippy
