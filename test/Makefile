TOOL_DIR = ../tools
SUITE_DIR = positive
CLAFER = ../clafer -s -v --tooldir=$(TOOL_DIR)
CLAFER_SELF = ../clafer -s -v --tooldir=../

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


	find $(SUITE_DIR)  -type f \( -iname "*.als" ! -iname "*.des.cfr" \) | xargs  -t -I % -L1 diff  % %.reg
clean:
	$(MAKE) -C $(SUITE_DIR) clean
	find . -type f -name '*~' -print0 | xargs -0 rm -f
	find . -type f -name '*.als' -print0 | xargs -0 rm -f
	find . -type f -name '*.cfr.des' -print0 | xargs -0 rm -f
	find . -type f -name '*.xml' -print0 | xargs -0 rm -f
	find . -type f -name '*~' -print0 | xargs -0 rm -f