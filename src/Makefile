define apPatch
	$(shell patch $(1) -N -r - Front/$(2).hs Front/$(2).patch 1>/dev/null)
endef

all:
	$(foreach file, Absclafer ErrM Lexclafer Printclafer Parclafer, \
		$(if $(call apPatch,--dry-run,$(file)), \
			$(call apPatch,,$(file))))
	ghc -outputdir dist/build --make dateVer -o dateVer
	./dateVer > Version.hs
	./Generator/quote.sh ClaferIR.xsd > ./Generator/Schema.hs

clean:
	$(MAKE) clean -C Front/
	rm -rf dist
	rm -r dateVer
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*.bak' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f
