SRC_DIR  = src
TEST_DIR = test
TOOL_DIR = tools

UNAME := $(shell uname -o | tr "A-Z" "a-z")

$(info os is $(UNAME))

ifeq ($(UNAME), cygwin)
	ifdef glpk
        GPLK_LIBS_INCLUDES := --extra-include-dirs=$(glpk)/src --extra-include-dirs=$(glpk)/src/amd --extra-include-dirs=$(glpk)/src/colamd --extra-include-dirs=$(glpk)/src/minisat --extra-include-dirs=$(glpk)/src/zlib --extra-lib-dirs=$(glpk)/w32	
	else
    	$(error Please provide the installation directory of WinGLPK 4.47 to the glpk parameter)
    endif
endif

all: build

install:  
	mkdir -p $(to)
	mkdir -p $(to)/tools
	cabal install --bindir=$(to) $(GPLK_LIBS_INCLUDES)
	cp -f README.md $(to)/clafer-README.md
	cp -f -r spl_configurator/py_src $(to)/
	cp -f  spl_configurator/clafer_moo.sh $(to)/
#   the following should be handled with cabal
	cp -f LICENSE $(to)/
	cp -f CHANGES $(to)/
	cp -f tools/alloy4.jar $(to)/tools
	cp -f tools/alloy4.2.jar $(to)/tools
	cp -f tools/alloy4moo.jar $(to)/tools
	cp -f tools/XsdCheck.class $(to)/tools

build:
	$(MAKE) -C $(TOOL_DIR)
	cabal install --only-dependencies $(GPLK_LIBS_INCLUDES)
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
