FRONT_DIR  = Language/Clafer/Front

define apPatch
	$(shell patch $(1) -N -r - $(2).hs $(2).diff 1>/dev/null)
endef

grammar:
	bnfc -p "Language.Clafer.Front" --ghc --pos clafer.cf
	happy -gca $(FRONT_DIR)/ParClafer.y
	alex -g $(FRONT_DIR)/LexClafer.x
	rm $(FRONT_DIR)/SkelClafer.hs
	rm $(FRONT_DIR)/TestClafer.hs
	mv $(FRONT_DIR)/DocClafer.txt ../doc
	rm $(FRONT_DIR)/*.bak

# before running grammarDoc it is necessary to manually modify the following rules in clafer.cf
# ModuleX.         Module ::= [Declaration] ;
# ClaferX.         Clafer ::= Abstract GCard PosIdent Super Reference Card Init Elements ;
# ConstraintX.     Constraint ::= "[" [Exp] "]" ;
# AssertionX.      Assertion ::= "assert" "[" [Exp] "]";
# AbstractX.       Abstract ::= "abstract" ;
# NCardX.          NCard  ::= PosInteger ".." ExInteger ;
# DeclX.           Decl ::= [LocId] ":" Exp15 ;
# the suffix "X" can be anything, it is needed only to avoid the error from the latex generator
# the names of the constructors do not appear in the generated LaTeX.
grammarDoc:
	bnfc --latex clafer.cf
	pdflatex clafer.tex
	mv clafer.pdf ../doc
	rm clafer.tex clafer.aux clafer.log

clean:
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*.bak' -print0 | xargs -0 rm -f
	find . -type f -name '*.log' -print0 | xargs -0 rm -f
	find . -type f -name '*.aux' -print0 | xargs -0 rm -f
	find . -type f -name '*.dvi' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f
