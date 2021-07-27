all: build test 

build: clean
	cargo build --release --example circ && ./scripts/build_mpc_zokrates_test.zsh && ./scripts/build_aby.zsh

test:
	cargo test && ./scripts/zokrates_test.zsh && python3 ./scripts/test_aby.py

aby:
	./scripts/zokrates_test.zsh && ./scripts/build_aby.zsh && python3 ./scripts/test_aby.py

clean:
	# reset ABY submodule
	git submodule update --init
	touch ./third_party/ABY/build && rm -r -- ./third_party/ABY/build 
	touch ./third_party/ABY/src/examples/2pc_* && rm -r -- ./third_party/ABY/src/examples/2pc_* 
	sed '/add_subdirectory.*2pc.*/d' -i ./third_party/ABY/src/examples/CMakeLists.txt 
