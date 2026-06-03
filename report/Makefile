# The `-interaction=nonstopmode -halt-on-error` arguments make LaTeX terminate on the first error.
# This makes it a bit nicer to use with IDE integration and is closer to the behavior of
# Overleaf which most people are familiar with.
#
# You can remove these arguments, if you want the default interactive behavior of LaTeX.
MAIN := thesis
BIB  := sources
BUILD:= build

./$(MAIN).pdf: main
	cp ./$(BUILD)/$(MAIN).pdf ./$(MAIN).pdf

main:
	latexmk -f -pdflua -synctex=1 -interaction=nonstopmode -halt-on-error -shell-escape -outdir=$(BUILD) $(MAIN)

clean:
	rm -R -f build/

