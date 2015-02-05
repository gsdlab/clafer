FRONT_DIR  = Language/Clafer/Front

define apPatch
	$(shell patch $(1) -N -r - $(2).hs $(2).diff 1>/dev/null)
endef

grammar:
	bnfc -p "Language.Clafer.Front" --ghc clafer.cf
	happy -gca $(FRONT_DIR)/Parclafer.y
	alex -g $(FRONT_DIR)/Lexclafer.x
	rm $(FRONT_DIR)/Skelclafer.hs
	rm $(FRONT_DIR)/Testclafer.hs
	rm $(FRONT_DIR)/*.bak
	mv $(FRONT_DIR)/Docclafer.txt ../doc

grammarDoc:
	bnfc --latex clafer.cf
	pdflatex $(FRONT_DIR)/Docclafer.tex

Schema.hs:
	./Language/Clafer/Generator/quote-xsd.sh Language/Clafer/ClaferIR.xsd > ./Language/Clafer/Generator/Schema.hs

Css.hs:
	./Language/Clafer/Generator/quote-css.sh Language/Clafer/clafer.css > ./Language/Clafer/Css.hs

clean:
	rm -rf dist
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*.bak' -print0 | xargs -0 rm -f
	find . -type f -name '*.log' -print0 | xargs -0 rm -f
	find . -type f -name '*.aux' -print0 | xargs -0 rm -f
	find . -type f -name '*.dvi' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f
