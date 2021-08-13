LATEX = latex
OTT = ott
OTT_FLAGS = -merge true #-show_defns false -show_sort false
PDFLATEX = texfot pdflatex

SOURCES = \
common.ott \
common_typing.ott \
arrow.ott \
# common_index.ott \
# common_labels.ott \
# bool.ott \
# bool_typing.ott \
# nat.ott \
# nat_typing.ott \
# basety.ott \
# unit.ott \
# seq.ott \
# ascribe.ott \
# let.ott \
# product.ott \
# sum.ott \
# fix.ott \
# tuple.ott \
# variant.ott

default: LambdaQs.pdf

LambdaQs.tex: $(SOURCES)
	$(OTT) $(OTT_FLAGS) -o LambdaQs.tex $(SOURCES)

#### TeX ####
.SUFFIXES: .tex .pdf
.tex.pdf:
	$(PDFLATEX) $<

#### Administrative targets ####
clean:
	rm -f LambdaQs.tex
	rm -f *.aux *.log *.pdf
