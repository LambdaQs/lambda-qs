genqsharp: QSharp.cf
	bnfc -mbnfc.mk --ocaml-menhir QSharp.cf && make all

genlambda: LambdaQs.cf
	bnfc -mbnfc.mk --ocaml-menhir LambdaQs.cf && make all

genhaskell: $(SRC).cf
	bnfc -mbnfc.mk $(SRC).cf && make all

genclean: clean
	rm -f Par*.ml Par*.mli Lex*.ml Test* *.bak

typing: Typ.ml
	utop -init Typ.ml

elab: Elab.ml genqsharp genlambda
	utop -init Elab.ml

sinclude bnfc.mk
