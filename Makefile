SRC_DIR  = src
TEST_DIR = test
TOOL_DIR = tools


all: build

install: all
	cabal install --bindir=.

build:
	$(MAKE) -C $(SRC_DIR)
	$(MAKE) -C $(TOOL_DIR)
	ghc -isrc -outputdir dist/build --make -O src/clafer -o clafer

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
	$(MAKE) -C $(TEST_DIR) clean
	$(MAKE) -C $(SRC_DIR) clean
	$(MAKE) -C $(TOOL_DIR) clean
	rm -rf dist
	rm -f clafer
	find . -type f -name '*.o' -print0 | xargs -0 rm -f
	find . -type f -name '*.hi' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f

deploy: 
	mkdir -p $(to)
	mkdir -p $(to)/tools
	cp tools/alloy4.jar $(to)/tools
	cp tools/alloy4.2-rc.jar $(to)/tools
	cp tools/XsdCheck.class $(to)/tools
	cp clafer $(to)
	cp clafer.exe $(to)
	cp README.md $(to)/clafer-README.md