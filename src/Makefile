OTT_SOURCE = LangE
OTT_LOC    = .
FILES      = $(OTT_SOURCE)_ott $(OTT_SOURCE)_inf
OTTFILES   = $(foreach i, $(OTT_SOURCE), $(OTT_LOC)/$(i).ott)
OTTIFLAGS  = $(foreach i, $(OTT_SOURCE), -i $(OTT_LOC)/$(i).ott)

LIBNAME=$(OTT_SOURCE)
LNGEN=../vendor/lngen/dist-newstyle/build/x86_64-*/ghc-*/lngen-0.3.1/x/lngen/build/lngen/lngen

## Include directories, one per line.

INCDIRS = \
        . \


VFILES   = $(foreach i, $(FILES), $(i).v)
INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

all: $(VFILES)

%_ott.v: $(OTT_LOC)/%.ott Makefile
	ott -i $(OTT_LOC)/$*.ott  -o $*_ott.v -coq_lngen true -coq_expand_list_types true
	make METALIB.FIX_$*_ott

%_inf.v: $(OTT_LOC)/%.ott Makefile
	$(LNGEN) --coq-no-proofs --coq $*_inf.v --coq-ott $*_ott $(OTT_LOC)/$*.ott

%_inf_proofs.v: $(OTT_LOC)/%.ott Makefile
	$(LNGEN) --coq $*_inf_proofs.v --coq-ott $*_ott $(OTT_LOC)/$*.ott


pdf: $(OTT_LOC)/$(OTT_SOURCE).ott
	ott -show_sort true -show_defns true -i $(OTT_LOC)/$(OTT_SOURCE).ott -o $(OTT_LOC)/$(OTT_SOURCE).tex
	texfot pdflatex $(OTT_LOC)/$(OTT_SOURCE).tex

ROOT            := LangE

OTT             := ott

MENHIR          := menhir

MENHIRFLAGS     := --infer

OCAMLBUILD      := ocamlbuild -use-ocamlfind -use-menhir -menhir "$(MENHIR) $(MENHIRFLAGS)"

MAIN            := main

mall: $(ROOT)_ast.ml $(ROOT)_parser.mly $(ROOT)_parser_pp.ml $(ROOT)_lexer.mll main.ml
	$(OCAMLBUILD) $(MAIN).byte


mpdf: $(ROOT)_quotiented.pdf $(ROOT)_unquotiented.pdf

# generate the ocaml AST type, ocamllex lexer, menhir parser, and ocaml pretty printers for the AST, all from the Ott soruce
$(ROOT)_ast.ml  $(ROOT)_lexer.mll $(ROOT)_parser.mly $(ROOT)_parser_pp.ml $(ROOT)_ast.tex : $(ROOT).ott
	$(OTT) -show_sort true -quotient_rules false -i $(ROOT).ott  -o $(ROOT)_parser.mly -o $(ROOT)_lexer.mll -o $(ROOT)_ast.ml -o $(ROOT).tex


$(ROOT)_quotiented.pdf: $(ROOT).ott Makefile
	$(OTT) -quotient_rules true -i $(ROOT).ott -o $(ROOT)_quotiented.tex
	pdflatex $(ROOT)_quotiented.tex

$(ROOT)_unquotiented.pdf: $(ROOT).ott Makefile
	$(OTT) -quotient_rules false -i $(ROOT).ott -o $(ROOT)_unquotiented.tex
	pdflatex $(ROOT)_unquotiented.tex

clean:
	@rm -f *~
	@rm -f *.log *.aux *.fls *.fdb_latexmk
	@rm -f $(VFILES)
	@rm -f *.pdf *.tex
	rm -rf _build
	rm -rf $(ROOT)_ast.ml $(ROOT)_parser.mly $(ROOT)_lexer.mll $(ROOT)_parser_pp.ml
	rm -rf *.aux *.log *.tex
	rm -rf main.native main.byte
	$(OCAMLBUILD) -clean

METALIB.FIX_%:
	sed -i -e 's/Metalib.Metatheory./Metalib.Metatheory. Require Export Metalib.LibLNgen. Global Set Warnings "-deprecated-hint-without-locality". /g' $*.v
	sed '1d' $*.v > __TMP__; mv __TMP__ $*.v
