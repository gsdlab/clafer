all:
	happy -gca ParLBNF.y
	alex -g LexLBNF.x
	latex DocLBNF.tex; dvips DocLBNF.dvi -o DocLBNF.ps
	ghc --make Rewrite.hs -o Rewrite
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocLBNF.ps
distclean: clean
	-rm -f DocLBNF.* LexLBNF.* ParLBNF.* LayoutLBNF.* SkelLBNF.* PrintLBNF.* TestLBNF.* AbsLBNF.* TestLBNF ErrM.* SharedString.* LBNF.dtd XMLLBNF.* Makefile*

