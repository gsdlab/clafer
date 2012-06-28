define apPatch
	$(shell patch $(1) -N -r - $(2).hs $(2).diff 1>/dev/null)
endef

all:
	$(MAKE) -C lbnf
	./lbnf/Rewrite clafer-orig.cf > clafer.cf
	bnfc clafer.cf
	patch Parclafer.y Parclafer.y.diff
	happy -gca Parclafer.y
	alex -g Lexclafer.x
#	latex Docclafer.tex; dvips Docclafer.dvi -o Docclafer.ps
	patch Absclafer.hs Absclafer.diff
	patch ErrM.hs ErrM.diff
	patch Lexclafer.hs Lexclafer.diff
	patch Printclafer.hs Printclafer.diff
	patch Parclafer.hs Parclafer.diff
#	$(foreach file, Absclafer ErrM Lexclafer Printclafer Parclafer, \
#		$(if $(call apPatch,--dry-run,$(file)), \
#			$(call apPatch,,$(file))))

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f Docclafer.ps
distclean: clean
	-rm -f Docclafer.* Lexclafer.* Parclafer.* Layoutclafer.* Skelclafer.* Printclafer.* Testclafer.* Absclafer.* Testclafer ErrM.* SharedString.* clafer.dtd XMLclafer.* Makefile*

