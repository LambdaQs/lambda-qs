SRC:=QSharp

gen: $(SRC).cf
	bnfc -mbnfc.mk --ocaml-menhir $(SRC).cf && make all

genclean: clean
	rm -f Par$(SRC).ml Par$(SRC).mli Lex$(SRC).ml Test$(SRC) *.bak

typing: Typ.ml
	utop -init Typ.ml

sinclude bnfc.mk
