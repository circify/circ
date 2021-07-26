all: build test 

build:
	cargo build --release --example circ && ./scripts/build_aby.zsh

test:
	cargo test && ./scripts/zokrates_test.zsh && python3 ./scripts/test_aby.py

aby:
	./scripts/zokrates_test.zsh && ./scripts/build_aby.zsh && python3 ./scripts/test_aby.py

