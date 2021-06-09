OTT_SOURCE = LambdaQs
OTT_LOC    = .
FILES      = LambdaQs_ott LambdaQs_inf
OTTFILES   = $(foreach i, LambdaQs, $(OTT_LOC)/$(i).ott)
OTTIFLAGS  = $(foreach i, LambdaQs, -i $(OTT_LOC)/$(i).ott)

LIBNAME=LambdaQs
LNGEN=lngen

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

clean:
	@rm -f *~
	@rm -f *.log *.aux *.fls *.fdb_latexmk
	@rm -f $(VFILES)
	@rm -f *.pdf *.tex

METALIB.FIX_%:
	sed -i -e 's/Metalib.Metatheory./Metalib.Metatheory. Require Export Metalib.LibLNgen. Global Set Warnings "-deprecated-hint-without-locality". /g' $*.v
	sed '1d' $*.v > __TMP__; mv __TMP__ $*.v
