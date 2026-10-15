SRC_DIR  := src
TEST_DIR := test
ifeq ($(OS),Windows_NT)
EXE := .exe
endif

ALLOY_JAR := alloy6.2.0.jar
ALLOY_URL := https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar

all: build

build: $(ALLOY_JAR)
	stack build

install:
	mkdir -p $(to)
	cp -f README.md $(to)/clafer-README.md
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f $(ALLOY_JAR) $(to)
	cp -f ecore2clafer.jar $(to)
	cp `stack path --local-install-root`/bin/clafer$(EXE) $(to)

# regenerate grammar, call after clafer.cf changed
grammar:
	$(MAKE) -C $(SRC_DIR) grammar

# Just like "init" but with enabled profiler
# this will reinstall everything with profiling support, build clafer, and copy it to .
prof: $(ALLOY_JAR)
	stack build --executable-profiling --library-profiling --ghc-options="-auto-all -caf-all -rtsopts -osuf p_o"

.PHONY: test
# Build first, so that the regression tests use the current compiler.
test: build
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

$(ALLOY_JAR):
	@echo "[WARNING] Missing $(ALLOY_JAR). Downloading..."
	curl -fsSL -o $(ALLOY_JAR) $(ALLOY_URL)
