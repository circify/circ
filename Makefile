all: test

fetch_deps:
	git submodule update --init

build_deps: fetch_deps
	./scripts/build_aby.zsh

build_aby_zokrates: build_deps build
	./scripts/build_mpc_zokrates_test.zsh
	./scripts/build_aby.zsh

build_aby_c: build_deps build
	./scripts/build_mpc_c_test.zsh
	./scripts/build_aby.zsh

build:
	cargo build --release --examples
	cargo build --examples

test: build build_aby_zokrates build_aby_c
	cargo test
	./scripts/zokrates_test.zsh
	python3 ./scripts/aby_tests/zokrates_test_aby.py
	python3 ./scripts/aby_tests/c_test_aby.py
	./scripts/test_zok_to_ilp.zsh
	./scripts/test_zok_to_ilp_pf.zsh
	./scripts/test_datalog.zsh

c_aby: build_aby_c
	python3 ./scripts/aby_tests/c_test_aby.py

z_aby: build_aby_zokrates
	python3 ./scripts/aby_tests/zokrates_test_aby.py

clean:
	# remove all generated files
	touch ./third_party/ABY/build && rm -r -- ./third_party/ABY/build 
	touch ./third_party/ABY/src/examples/2pc_* && rm -r -- ./third_party/ABY/src/examples/2pc_* 
	sed '/add_subdirectory.*2pc.*/d' -i ./third_party/ABY/src/examples/CMakeLists.txt 
	rm -rf ./third_party/ABY/src/examples/2pc_*.txt
	rm -rf scripts/aby_tests/__pycache__
	rm -rf P V pi perf.data perf.data.old flamegraph.svg

format:
	cargo fmt --all

lint:
	cargo clippy
