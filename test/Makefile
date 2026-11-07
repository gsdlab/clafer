SUITE_DIR = positive
REG_DIR = regression
CLAFER = ../clafer -s -v -k --tooldir=..
# the number of models compiled and validated at a time, e.g., make test JOBS=4
JOBS ?= $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

UNAME := $(shell uname | tr "A-Z" "a-z")

ifeq ($(UNAME), darwin)
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \)   | sed s/$(SUITE_DIR)\\///
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \)   | sed s/$(SUITE_DIR)\\///
    FIND_DES_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.des.cfr" \)   | sed s/$(SUITE_DIR)\\///
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \)   | sed s/$(SUITE_DIR)\\///
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \)   | sed s/$(SUITE_DIR)\\///
else
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \) -printf "%f\n"
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \) -printf "%f\n"
    FIND_DES_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.des.cfr" \) -printf "%f\n"
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \) -printf "%f\n"
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \) -printf "%f\n"
endif


ifeq ($(UNAME), darwin)
    XARGS_CP_REGS :=  xargs  -t -I % -L1 cp  $(SUITE_DIR)/% $(REG_DIR)/%.reg
else
    XARGS_CP_REGS := xargs  -t -i cp $(SUITE_DIR)/{} $(REG_DIR)/{}.reg
endif


test:
	@echo "========================"
	@echo "| Beginning testing of |"
	@echo "========================"
	@$(CLAFER) -V
	$(MAKE) clean
	@# diff the regressions also when a model fails, and fail if either fails
	@$(MAKE) generateAlloyJSHTMLDot; generated=$$?; \
	$(MAKE) diffRegressions; regressions=$$?; \
	test $$generated -eq 0 -a $$regressions -eq 0

generateAlloyJSHTMLDot:
	@echo "==================================================================================="
	@echo "| Testing 'Positive' suite - generating Alloy, JavaScript, HTML, and Graph output |"
	@echo "|                          and the explicit form (-m clafer)                      |"
	@echo "|                          - validating them: Alloy and chocosolver run them,     |"
	@echo "|                            dot draws the graphs, the explicit form compiles to  |"
	@echo "|                            itself                                                |"
	@echo "==================================================================================="

	@if test ! -f "../alloy6.2.0.jar"; then \
		echo "[ERROR] Missing ../alloy6.2.0.jar."; false; \
	fi

	@if test ! -f "../chocosolver.jar"; then \
		echo "[ERROR] Missing ../chocosolver.jar."; false; \
	fi

	@# Compile the positive test suite to Alloy, Choco, the explicit form, HTML, and Graph,
	@# and validate the outputs, $(JOBS) models at a time; fails, after all the models, if one
	@# fails to compile or an output fails to validate (a counterexample is not a failure)
	@bash compile-positive.sh $(SUITE_DIR) $(JOBS) $(CLAFER) -m=alloy -m=choco -m=clafer -m=html -m=graph --self-contained

diffRegressions:
	@echo "======================================================="
	@echo "| Testing 'Positive' suite - Diffing with regressions |"
	@echo "======================================================="
	@# Fails if an output differs, has no regression, or a regression has no output;
	@# the outputs become the new regressions, to be reviewed and committed.
	@bash diff-regressions.sh $(SUITE_DIR) $(REG_DIR)

reg:
	@echo "============================"
	@echo "| Creating new regressions |"
	@echo "============================"
	@rm $(REG_DIR)/*.reg
	$(MAKE) newReg

newReg:
	@echo "---------------------"
	@echo "| Alloy regressions |"
	@echo "---------------------"
	@$(FIND_ALS_COMMAND) | $(XARGS_CP_REGS)
	@echo "---------------------"
	@echo "| Choco regressions |"
	@echo "---------------------"
	@$(FIND_JS_COMMAND) | $(XARGS_CP_REGS)
	@echo "-------------------------------"
	@echo "| Explicit form regressions |"
	@echo "-------------------------------"
	@$(FIND_DES_COMMAND) | $(XARGS_CP_REGS)
	@echo "---------------------"
	@echo "| HTML regressions |"
	@echo "---------------------"
	@$(FIND_HTML_COMMAND) | $(XARGS_CP_REGS)
	@echo "----------------------"
	@echo "| Graph regressions |"
	@echo "----------------------"
	@$(FIND_DOT_COMMAND) | $(XARGS_CP_REGS)
	@echo "----------------------------"
	@echo "| Adding to Git repository |"
	@echo "----------------------------"
	@git add $(REG_DIR)/*.reg

clean:
	@echo "==============="
	@echo "| Cleaning up |"
	@echo "==============="
	@echo ""
	@# Only the outputs generated in $(SUITE_DIR), so that tracked files with
	@# these extensions in other directories are kept.
	@echo 'Removing $(SUITE_DIR)/*.als, *.js, *.des.cfr, *.html, *.dot, *.dot.svg'
	@find $(SUITE_DIR) -type f \( -name '*.als' -o -name '*.js' -o -name '*.des.cfr' -o -name '*.html' -o -name '*.dot' -o -name '*.dot.svg' \) -print0 | xargs -0 rm -f
	@echo 'Removing *~'
	@find . -type f -name '*~' -print0 | xargs -0 rm -f
