TOOL_DIR = ../tools
SUITE_DIR = positive
REG_DIR = regression
CLAFER = ../clafer -s -v --tooldir=$(TOOL_DIR)
CLAFER_SELF = ../clafer -s -v --tooldir=../

UNAME := $(shell uname | tr "A-Z" "a-z")

ifeq ($(UNAME), darwin)
	FIND_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" ! -iname "*.des.als" \)   | sed s/$(SUITE_DIR)\\///  
	XARGS_DIFF_COMMAND := xargs  -t -I % -L1 diff -w -B  $(SUITE_DIR)/% $(REG_DIR)/%.reg
else
	FIND_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" ! -iname "*.des.als" \) -printf "%f\n"
	XARGS_DIFF_COMMAND := xargs  -t -i diff -w -B $(REG_DIR)/{}.reg $(SUITE_DIR)/{}
endif


ifeq ($(UNAME), darwin)
	XARGS_CP_REGS :=  xargs  -t -I % -L1 cp  $(SUITE_DIR)/% $(REG_DIR)/%.reg 
else
       	XARGS_CP_REGS := xargs  -t -i cp $(REG_DIR)/{}.reg $(SUITE_DIR)/{}
endif


test:
	$(MAKE) clean
	@if test ! -f $(TOOL_DIR)/"alloy4.jar"; then \
		echo "[ERROR] Missing $(TOOL_DIR)/alloy4.jar."; false; \
	fi

	find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) |  xargs -L1 $(CLAFER)

	@if test ! -f $(TOOL_DIR)/"XsdCheck.class"; then \
		echo "[ERROR] Missing $(TOOL_DIR)/XsdCheck.class."; false; \
	fi

	echo "Testing 'Positive' Suite for expected output to match" 

	find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) | xargs -L1 $(CLAFER) -m=xml
	find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) | xargs -L1 $(CLAFER_SELF) -m=clafer


	$(FIND_COMMAND) | $(XARGS_DIFF_COMMAND)

reg:

	rm $(REG_DIR)/*.reg

	$(FIND_COMMAND) | $(XARGS_CP_REGS)	

clean:
	$(MAKE) -C $(SUITE_DIR) clean
	find . -type f -name '*~' -print0 | xargs -0 rm -f
	find . -type f -name '*.als' -print0 | xargs -0 rm -f
	find . -type f -name '*.cfr.des' -print0 | xargs -0 rm -f
	find . -type f -name '*.xml' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f