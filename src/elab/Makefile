default: genqsharp genlambda

genqsharp: QSharp.cf
	bnfc -mbnfc.mk --ocaml-menhir QSharp.cf && make all

genlambda: LambdaQs.cf
	bnfc -mbnfc.mk --ocaml-menhir LambdaQs.cf && make all

genhaskell: QSharp.cf
	bnfc -mbnfc.mk QSharp.cf && make all

genclean:
	rm -f Par*.ml Par*.mli Lex*.ml Test* *.bak

typing: Typ.ml
	utop -init Typ.ml

sinclude bnfc.mk
