SRC_DIR  := src
TEST_DIR := test
TOOL_DIR := tools

ifeq ($(OS),Windows_NT)
	GPLK_LIBS_INCLUDES := --extra-include-dirs=$(glpk)/src --extra-include-dirs=$(glpk)/src/amd --extra-include-dirs=$(glpk)/src/colamd --extra-include-dirs=$(glpk)/src/minisat --extra-include-dirs=$(glpk)/src/zlib --extra-lib-dirs=$(glpk)/w32
else
	UNAME_S := $(shell uname -s)
	ifeq ($(UNAME_S),Darwin)
	MAC_USR_LIB := --extra-lib-dir=/opt/local/lib --extra-include-dir=/opt/local/include/
	endif
endif

all: build

init:
	cabal sandbox init --sandbox=../.clafertools-cabal-sandbox
	# Uncomment to use Haskell LTS in the sandbox
	# wget http://www.stackage.org/snapshot/lts-1.4/cabal.config
	# mv cabal.config ../.clafertools-cabal-sandbox
	# the constraint is there to prevent installing utf8-string-1 which conflicts with gitit, which requires utf8-string <= 0.3.8.
	cabal install --only-dependencies $(GPLK_LIBS_INCLUDES) $(MAC_USR_LIB) --enable-tests --constraint="utf8-string==0.3.8"

build:
	$(MAKE) -C $(TOOL_DIR)
	cabal configure
	cabal build

install:
	mkdir -p $(to)
	mkdir -p $(to)/tools
	cp -f README.md $(to)/clafer-README.md
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f tools/alloy4.2.jar $(to)/tools
	cp -f tools/XsdCheck.class $(to)/tools
	cp -f tools/ecore2clafer.jar $(to)/tools
	if test "$(glpk)" ; then cp -f $(glpk)/w32/glpk_4_55.dll $(to); fi
	cabal install --bindir=$(to) $(GPLK_LIBS_INCLUDES) $(MAC_USR_LIB) --ghc-option="-O"

# Removes current build and makes a clean new one (Don't use if starting from scratch!)
cleanEnv:
	make clean
	ghc-pkg unregister clafer --package-db=../.clafertools-cabal-sandbox/x86_64-windows-ghc-7.8.3
	rm `which clafer`
	make

# regenerate grammar, call after clafer.cf changed
grammar:
	$(MAKE) -C $(SRC_DIR) grammar

# build Schema.hs from ClaferIG.xsd, call after .xsd changed
Schema.hs:
	$(MAKE) -C $(SRC_DIR) Schema.hs

# build Css.hs from clafer.css, call after .css changed
Css.hs:
	$(MAKE) -C $(SRC_DIR) Css.hs

# enable profiler
# first remove `cabal` and `ghc` folders (on win: `<User>\AppData\Roaming\cabal` and `<User>\AppData\Roaming\ghc`)
# this will reinstall everything with profiling support, build clafer, and copy it to .
prof:
	cabal update
	cabal install --only-dependencies -p --enable-executable-profiling $(GPLK_LIBS_INCLUDES) $(MAC_USR_LIB)
	cabal configure -p --enable-executable-profiling
	cabal build --ghc-options="-prof -auto-all -rtsopts"

.PHONY : test

test:
	cabal test
	$(MAKE) -C $(TEST_DIR) test

generateAlloyJSPythonXMLXHTMLDot:
	$(MAKE) -C $(TEST_DIR) generateAlloyJSPythonXMLXHTMLDot

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
