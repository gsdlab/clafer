SRC_DIR  := src
TEST_DIR := test
TOOL_DIR := tools

ifeq ($(OS),Windows_NT)

else
	UNAME_S := $(shell uname -s)
	ifeq ($(UNAME_S),Darwin)
	MAC_USR_LIB := --extra-lib-dir=/opt/local/lib --extra-include-dir=/opt/local/include/
	endif
endif

all: build

init:
	cabal sandbox init --sandbox=../.clafertools-cabal-sandbox
	cabal install --only-dependencies $(MAC_USR_LIB) --enable-tests

build:
	$(MAKE) -C $(TOOL_DIR)
	cabal configure --enable-tests
	cabal build

install:
	mkdir -p $(to)
	mkdir -p $(to)/tools
	cp -f README.md $(to)/clafer-README.md
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f tools/alloy4.2.jar $(to)/tools
	cp -f tools/ecore2clafer.jar $(to)/tools
	cabal install --bindir=$(to) $(GPLK_LIBS_INCLUDES) $(MAC_USR_LIB) --enable-optimization=2

# Removes current build and makes a clean new one (Don't use if starting from scratch!)
cleanEnv:
	make clean
	cabal sandbox hc-pkg unregister clafer
	rm `which clafer`
	make

# regenerate grammar, call after clafer.cf changed
grammar:
	$(MAKE) -C $(SRC_DIR) grammar

# build Css.hs from clafer.css, call after .css changed
Css.hs:
	$(MAKE) -C $(SRC_DIR) Css.hs

# Just like "init" but with enabled profiler
# this will reinstall everything with profiling support, build clafer, and copy it to .
prof:
	rm -rf ../.clafertools-cabal-sandbox
	cabal sandbox init --sandbox=../.clafertools-cabal-sandbox
	cabal install --only-dependencies $(MAC_USR_LIB) --enable-tests -p --enable-executable-profiling --enable-library-profiling
	$(MAKE) -C $(TOOL_DIR)
	cabal configure -p --enable-executable-profiling --enable-library-profiling
	cabal build --ghc-options="-prof -fprof-auto -auto-all -caf-all -rtsopts -osuf p_o"

.PHONY : test

test:
	cabal test
	$(MAKE) -C $(TEST_DIR) test

generateAlloyJSPythonHTMLDot:
	$(MAKE) -C $(TEST_DIR) generateAlloyJSPythonHTMLDot

diffRegressions:
	$(MAKE) -C $(TEST_DIR) diffRegressions

reg:
	$(MAKE) -C $(TEST_DIR) reg

clean:
	rm -f clafer
	cabal clean
	$(MAKE) -C $(SRC_DIR) clean
	$(MAKE) -C $(TOOL_DIR) clean
	$(MAKE) cleanTest

cleanTest:
	$(MAKE) -C $(TEST_DIR) clean

tags:
	hasktags --ctags --extendedctag .
