all: build test 

build:
	cargo build --release --example circ && ./scripts/build_mpc_zokrates_test.zsh && ./scripts/build_aby.zsh

test:
	cargo test && ./scripts/zokrates_test.zsh && python3 ./scripts/test_aby.py

aby:
	./scripts/zokrates_test.zsh && ./scripts/build_aby.zsh && python3 ./scripts/test_aby.py

clean:
	rm -r ./third_party/ABY/build