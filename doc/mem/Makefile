.PHONY: main.pdf auto clean sync
main: build/main.pdf

build/main.pdf:
	latexmk -pdf -halt-on-error -interaction=nonstopmode -shell-escape main.tex -outdir=build

auto:
	latexmk -pvc -pdf -halt-on-error -interaction=nonstopmode -shell-escape main.tex -outdir=build

clean:
	latexmk -C main.tex
	rm -rf build
