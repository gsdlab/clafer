SRC_DIR  := src
TEST_DIR := test
TOOL_DIR := tools
UNAME := $(shell uname -o | tr "A-Z" "a-z")

ifeq ($(UNAME), cygwin)
	GPLK_LIBS_INCLUDES := --extra-include-dirs=$(glpk)/src --extra-include-dirs=$(glpk)/src/amd --extra-include-dirs=$(glpk)/src/colamd --extra-include-dirs=$(glpk)/src/minisat --extra-include-dirs=$(glpk)/src/zlib --extra-lib-dirs=$(glpk)/w32	
endif
ifeq ($(UNAME), windows)
	GPLK_LIBS_INCLUDES := --extra-include-dirs=$(glpk)/src --extra-include-dirs=$(glpk)/src/amd --extra-include-dirs=$(glpk)/src/colamd --extra-include-dirs=$(glpk)/src/minisat --extra-include-dirs=$(glpk)/src/zlib --extra-lib-dirs=$(glpk)/w32	
endif
ifeq ($(UNAME), msys)
	GPLK_LIBS_INCLUDES := --extra-include-dirs=$(glpk)/src --extra-include-dirs=$(glpk)/src/amd --extra-include-dirs=$(glpk)/src/colamd --extra-include-dirs=$(glpk)/src/minisat --extra-include-dirs=$(glpk)/src/zlib --extra-lib-dirs=$(glpk)/w32	
endif
ifeq ($(UNAME), darwin)
	MAC_USR_LIB := --extra-lib-dir=/usr/lib
endif

all: build

build:
	$(MAKE) -C $(TOOL_DIR)
	cabal install --only-dependencies $(GPLK_LIBS_INCLUDES) $(MAC_USR_LIB)
	cabal configure
	cabal build

install:  
	mkdir -p $(to)
	mkdir -p $(to)/tools
	cp -f README.md $(to)/clafer-README.md
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f tools/alloy4.jar $(to)/tools
	cp -f tools/alloy4.2.jar $(to)/tools
	cp -f tools/XsdCheck.class $(to)/tools
	cp -f tools/ecore2clafer.jar $(to)/tools
	cp -f -R IDEs $(to)/
	if test "$(glpk)" ; then cp -f $(glpk)/w32/glpk_4_49.dll $(to); fi
	cabal install --bindir=$(to) $(GPLK_LIBS_INCLUDES) $(MAC_USR_LIB)

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
	cabal configure --enable-tests
	cabal build
	cabal test	
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