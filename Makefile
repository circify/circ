test:
	cargo test && ./scripts/zokrates_test.zsh

compile_aby:
	./scripts/compile_aby.zsh
	
test_aby:
	./scripts/zokrates_test.zsh && ./scripts/compile_aby.zsh && python3 ./scripts/aby_test.py

