FIGS		= MonoidSyntax
PGFS		= $(patsubst %, %.pgf, $(FIGS))
DIAGRAMS	= stack exec --package diagrams-pgf --package diagrams --package extra

all: FreeHIT.pdf

FreeHIT.pdf: FreeHIT.lagda.md header.tex $(PGFS)
	pandoc \
	  -H header.tex -t beamer \
	  --pdf-engine=xelatex \
	  -o $@ $<

$(PGFS): Figs.hs
	$(DIAGRAMS) -- runhaskell $<

