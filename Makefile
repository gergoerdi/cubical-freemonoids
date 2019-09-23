all: FreeHIT.pdf

%.pdf: %.md header.tex
	pandoc \
	  -H header.tex -t beamer \
	  --pdf-engine=xelatex \
	  -o $@ $<

