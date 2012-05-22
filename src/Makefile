all:
	$(MAKE) -C Front
	./Generator/quote.sh ClaferIR.xsd > ./Generator/Schema.hs

newVersion:
	ghc -isrc dateVer.hs ../dist/build/autogen/Paths_clafer.hs -outputdir dist/build --make -o dateVer
	./dateVer > Version.hs

clean:
	$(MAKE) clean -C Front/
	rm -rf dist
	rm -r dateVer
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*.bak' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f
