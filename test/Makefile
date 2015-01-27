TOOL_DIR = ../tools
SUITE_DIR = positive
REG_DIR = regression
CLAFER = ../dist/build/clafer/clafer -s -v -k --tooldir=$(TOOL_DIR)

UNAME := $(shell uname | tr "A-Z" "a-z")

ifeq ($(UNAME), darwin)
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \)   | sed s/$(SUITE_DIR)\\///
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \)   | sed s/$(SUITE_DIR)\\///
    FIND_PY_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.py" \)   | sed s/$(SUITE_DIR)\\///
    FIND_XML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.xml" \)   | sed s/$(SUITE_DIR)\\///
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \)   | sed s/$(SUITE_DIR)\\///
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \)   | sed s/$(SUITE_DIR)\\///
    XARGS_DIFF_COMMAND := xargs  -t -I % -L1 diff -w -B  $(SUITE_DIR)/% $(REG_DIR)/%.reg
else
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \) -printf "%f\n"
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \) -printf "%f\n"
    FIND_PY_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.py" \) -printf "%f\n"
    FIND_XML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.xml" \) -printf "%f\n"
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \) -printf "%f\n"
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \) -printf "%f\n"
    XARGS_DIFF_COMMAND := xargs  -t -i diff -w -B $(REG_DIR)/{}.reg $(SUITE_DIR)/{}
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
	$(MAKE) generateAlloyJSPythonXMLXHTMLDot
	$(MAKE) diffRegressions

generateAlloyJSPythonXMLXHTMLDot:
	@echo "========================================================================================"
	@echo "| Testing 'Positive' suite - generating Alloy, JS, Python, XML, HTML, and Graph output |"
	@echo "|                          - validating Alloy and XML output                           |"
	@echo "========================================================================================"

	@if test ! -f $(TOOL_DIR)/"alloy4.2.jar"; then \
		echo "[ERROR] Missing $(TOOL_DIR)/alloy4.2.jar."; false; \
	fi

	@if test ! -f $(TOOL_DIR)/"XsdCheck.class"; then \
		echo "[ERROR] Missing $(TOOL_DIR)/XsdCheck.class."; false; \
	fi

	# Compile the positive test suite to Alloy, Choco, Python, XML, HTML, and Graph
	@find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) |  xargs -L1 $(CLAFER) -m=alloy42 -m=choco -m=python -m=xml -m=html -m=graph ; true ; \

diffRegressions:
	@echo "======================================================="
	@echo "| Testing 'Positive' suite - Diffing with regressions |"
	@echo "======================================================="

	@echo "---------------------"
	@echo "| Alloy regressions |"
	@echo "---------------------"
	@$(FIND_ALS_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "---------------------"
	@echo "| Choco regressions |"
	@echo "---------------------"
	@$(FIND_JS_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "----------------------"
	@echo "| Python regressions |"
	@echo "----------------------"
	@$(FIND_PY_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "-------------------"
	@echo "| XML regressions |"
	@echo "-------------------"
	@$(FIND_XML_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "--------------------"
	@echo "| HTML regressions |"
	@echo "--------------------"
	@$(FIND_HTML_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "---------------------"
	@echo "| Graph regressions |"
	@echo "---------------------"
	@$(FIND_DOT_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

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
	@echo "----------------------"
	@echo "| Python regressions |"
	@echo "----------------------"
	@$(FIND_PY_COMMAND) | $(XARGS_CP_REGS)
	@echo "---------------------"
	@echo "| XML regressions |"
	@echo "---------------------"
	@$(FIND_XML_COMMAND) | $(XARGS_CP_REGS)
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
	@echo 'Removing *.als'
	@find . -type f -name '*.als' -print0 | xargs -0 rm -f
	@echo 'Removing *.js'
	@find . -type f -name '*.js' -print0 | xargs -0 rm -f
	@echo 'Removing *.py'
	@find . -type f -name '*.py' -print0 | xargs -0 rm -f
	@echo 'Removing *.xml'
	@find . -type f -name '*.xml' -print0 | xargs -0 rm -f
	@echo 'Removing *.html'
	@find . -type f -name '*.html' -print0 | xargs -0 rm -f
	@echo 'Removing *.dot'
	@find . -type f -name '*.dot' -print0 | xargs -0 rm -f
	@echo 'Removing *~'
	@find . -type f -name '*~' -print0 | xargs -0 rm -f
