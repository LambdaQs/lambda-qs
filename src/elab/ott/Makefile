FILE=LambdaQs

.PHONY: clean pdf

$(FILE).tex: $(FILE).ott
	ott -show_sort true -show_defns true -i $(FILE).ott -o $(FILE).tex

$(FILE).pdf: $(FILE).tex
	texfot pdflatex $(FILE).tex

pdf: $(FILE).pdf

clean:
	rm -f *.aux *.log *.pdf *.tex
