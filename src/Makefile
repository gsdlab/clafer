FRONT_DIR  = Language/Clafer/Front

define apPatch
	$(shell patch $(1) -N -r - $(2).hs $(2).diff 1>/dev/null)
endef

grammar:
	bnfc -p "Language.Clafer.Front" --ghc clafer.cf
#	patch Parclafer.y Parclafer.y.diff
#	happy -gca Parclafer.y
#	alex -g Lexclafer.x
#	latex Docclafer.tex; dvips Docclafer.dvi -o Docclafer.ps
#	patch Absclafer.hs Absclafer.diff
#	patch ErrM.hs ErrM.diff
#	patch Lexclafer.hs Lexclafer.diff
#	patch Printclafer.hs Printclafer.diff
#	patch Parclafer.hs Parclafer.diff
#	$(foreach file, Absclafer ErrM Lexclafer Printclafer Parclafer, \
#		$(if $(call apPatch,--dry-run,$(file)), \
#			$(call apPatch,,$(file))))

Schema.hs:
	./Language/Clafer/Generator/quote-xsd.sh Language/Clafer/ClaferIR.xsd > ./Language/Clafer/Generator/Schema.hs
	
Css.hs:
	./Language/Clafer/Generator/quote-css.sh Language/Clafer/clafer.css > ./Language/Clafer/Css.hs

clean:
	$(MAKE) clean -C $(FRONT_DIR)
	rm -rf dist 
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*.bak' -print0 | xargs -0 rm -f
	find . -type f -name '*.log' -print0 | xargs -0 rm -f
	find . -type f -name '*.aux' -print0 | xargs -0 rm -f
	find . -type f -name '*.dvi' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f