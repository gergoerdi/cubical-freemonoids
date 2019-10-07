all: FreeHIT.pdf

%.pdf: %.lagda.md header.tex
	pandoc \
	  -H header.tex -t beamer \
	  --pdf-engine=xelatex \
	  -o $@ $<

