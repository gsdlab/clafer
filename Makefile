SRC_DIR  = src
TEST_DIR = test
TOOL_DIR = tools

all: build

install:  
	mkdir -p $(to)
	mkdir -p $(to)/tools
	cabal install --bindir=$(to)
	cp -f README.md $(to)/clafer-README.md
#   the following should be handled with cabal
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f tools/alloy4.jar $(to)/tools
	cp -f tools/alloy4.2.jar $(to)/tools
	cp -f tools/XsdCheck.class $(to)/tools

build:
	$(MAKE) -C $(TOOL_DIR)
	cabal install --only-dependencies
	cabal configure
	cabal build
	cp dist/build/clafer/clafer .

# build Schema.hs from ClaferIG.xsd, call after .xsd changed
Schema.hs:
	$(MAKE) -C $(SRC_DIR) Schema.hs

# build Css.hs from clafer.css, call after .css changed
Css.hs:
	$(MAKE) -C $(SRC_DIR) Css.hs

# enable profiler
prof:
	$(MAKE) -C $(SRC_DIR)
	$(MAKE) -C $(TOOL_DIR)
	ghc -isrc -prof -auto-all -rtsopts -O -outputdir dist/build --make src/clafer -o clafer

.PHONY : test

test:
	$(MAKE) -C $(TEST_DIR) test

reg:
	$(MAKE) -C $(TEST_DIR) reg

newVersion:
	$(MAKE) -C $(SRC_DIR) newVersion

clean:
	rm -f clafer
	rm -rf dist
	$(MAKE) -C $(TEST_DIR) clean
	$(MAKE) -C $(SRC_DIR) clean
	$(MAKE) -C $(TOOL_DIR) clean
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f
