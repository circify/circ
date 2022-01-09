all: build test 

build: init
	cargo build --release --example circ && \
	./scripts/build_mpc_zokrates_test.zsh && \
	./scripts/build_mpc_c_test.zsh && \
	./scripts/build_aby.zsh

test:
	cargo test && \
	./scripts/zokrates_test.zsh && \
	python3 ./scripts/aby_tests/zokrates_test_aby.py &&  \
	python3 ./scripts/aby_tests/c_test_aby.py &&  \
	./scripts/test_zok_to_ilp.zsh && \
	./scripts/test_zok_to_ilp_pf.zsh && \
	./scripts/test_datalog.zsh 
	# ./scripts/test_c_pf.zsh

test_zkp:
	cargo test && \
	./scripts/zokrates_test.zsh && \
	./scripts/test_zok_to_ilp_pf.zsh && \
	./scripts/test_datalog.zsh && \
	./scripts/test_c_pf.zsh

init:
	git submodule update --init

c_aby:
	./scripts/build_mpc_c_test.zsh && \
	./scripts/build_aby.zsh && \
	python3 ./scripts/aby_tests/c_test_aby.py

z_aby:
	./scripts/build_mpc_zokrates_test.zsh && \
	./scripts/build_aby.zsh && \
	python3 ./scripts/aby_tests/zokrates_test_aby.py

clean:
	# remove all generated files
	touch ./third_party/ABY/build && rm -r -- ./third_party/ABY/build 
	touch ./third_party/ABY/src/examples/2pc_* && rm -r -- ./third_party/ABY/src/examples/2pc_* 
	sed '/add_subdirectory.*2pc.*/d' -i ./third_party/ABY/src/examples/CMakeLists.txt 
	rm -r ./third_party/ABY/src/examples/2pc_*.txt
	rm -r scripts/aby_tests/__pycache__*
	rm -rf P V pi perf.data perf.data.old flamegraph.svg

format:
	cargo fmt --all

lint:
	cargo clippy
