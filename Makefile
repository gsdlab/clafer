SRC_DIR  := src
TEST_DIR := test
ifeq ($(OS),Windows_NT)
EXE := .exe
endif

all: build

build: alloy4.2.jar
	stack build

install:
	mkdir -p $(to)
	cp -f README.md $(to)/clafer-README.md
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f alloy4.2.jar $(to)
	cp -f ecore2clafer.jar $(to)
	cp `stack path --local-install-root`/bin/clafer$(EXE) $(to)

# regenerate grammar, call after clafer.cf changed
grammar:
	$(MAKE) -C $(SRC_DIR) grammar

# Just like "init" but with enabled profiler
# this will reinstall everything with profiling support, build clafer, and copy it to .
prof: alloy4.2.jar
	stack build --executable-profiling --library-profiling --ghc-options="-auto-all -caf-all -rtsopts -osuf p_o"

.PHONY: test
test:
	cp `stack path --local-install-root`/bin/clafer$(EXE) .
	stack test 2>/dev/null || :    # supress error message and exit code if fail
	$(MAKE) -C $(TEST_DIR) test

generateAlloyJSHTMLDot:
	$(MAKE) -C $(TEST_DIR) generateAlloyJSHTMLDot

diffRegressions:
	$(MAKE) -C $(TEST_DIR) diffRegressions

reg:
	$(MAKE) -C $(TEST_DIR) reg

.PHONY: clean
clean:
	$(MAKE) -C $(SRC_DIR) clean
	$(MAKE) cleanTools
	$(MAKE) cleanTest
	stack clean

.PHONY: cleanTest
cleanTest:
	$(MAKE) -C $(TEST_DIR) clean

.PHONY: cleanTools
cleanTools:
	find . -type f -name '*.class' -print0 | xargs -0 rm -f

.PHONY: tags
tags:
	hasktags --ctags --extendedctag --ignore-close-implementation .

.PHONY: codex
codex:
	codex update
	mv codex.tags tags

WGET_COMMAND := wget
ifeq ($(OS),Windows_NT)
	ifeq ($(shell which wget), which: wget: unkown command)
		pacman -S make wget
	endif
else
	UNAME_S := $(shell uname -s)
	ifeq ($(UNAME_S),Darwin)
		WGET_COMMAND := curl -O
	endif
endif

alloy4.2.jar:
	@if test ! -f "alloy4.2.jar"; then \
		echo "[WARNING] Missing alloy4.2.jar. Downloading...";  \
		$(WGET_COMMAND) http://alloy.mit.edu/alloy/downloads/alloy4.2_2015-02-22.jar; \
		mv alloy4.2_2015-02-22.jar alloy4.2.jar; \
	fi
