all: FreeHIT.pdf

%.pdf: %.md header.tex
	pandoc \
		--pdf-engine=xelatex \
		-H header.tex -t beamer \
		$< -o $@

