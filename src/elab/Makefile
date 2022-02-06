default: genqsharp genlambda

genqsharp: QSharp.cf
	bnfc -mbnfc.mk --ocaml-menhir QSharp.cf && make all

genlambda: LambdaQs.cf
	bnfc -mbnfc.mk --ocaml-menhir LambdaQs.cf && make all

genhaskell: QSharp.cf
	bnfc -mbnfc.mk QSharp.cf && make all

genclean: clean
	rm -f Par*.ml Par*.mli Lex*.ml Test* *.bak

cleanall: genclean
	rm -f *.mll *.mly *QSharp.ml *LambdaQs.ml bnfc.mk BNFC_Util.ml

typing: Typ.ml genlambda
	utop -init Typ.ml

sinclude bnfc.mk
