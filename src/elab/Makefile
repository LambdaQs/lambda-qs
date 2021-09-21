SRC:=LambdaQs

sinclude bnfc.mk

gen:
	bnfc -mbnfc.mk --ocaml-menhir $(SRC).cf && make all

genclean: clean
	rm -f Par$(SRC).ml Par$(SRC).mli Lex$(SRC).ml Test$(SRC)
