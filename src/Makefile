define apPatch
	$(shell patch $(1) -N -r - Front/$(2).hs Front/$(2).patch 1>/dev/null)
endef

all:
#	cat Generator/XmlHeader.hs > Generator/XmlHelp.hs
#	DrIFT -r Front/Absclafer.hs >> Generator/XmlHelp.hs
#	DrIFT -r Intermediate/Intclafer.hs >> Generator/XmlHelp.hs
	$(foreach file, Absclafer ErrM Lexclafer Printclafer Parclafer, \
		$(if $(call apPatch,--dry-run,$(file)), \
			$(call apPatch,,$(file))))
	ghc --make dateVer
	./dateVer > Version.hs
	./Generator/quote.sh Generator/ClaferIR.xsd > ./Generator/Schema.hs
	javac XsdCheck.java
	ghc --make -O clafer

prof:
	ghc -prof -auto-all -rtsopts -O --make clafer

test:
	find ./Test/suite -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) | xargs -L1 ./clafer -s

clean:
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f
