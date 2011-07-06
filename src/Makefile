all:
	ghc --make -O clafer
clean:
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f
