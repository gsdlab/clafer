TOOL_DIR = ../tools
SUITE_DIR = suite
CLAFER = ../clafer -s -v --tooldir=$(TOOL_DIR)

test:
	$(MAKE) clean
	@if test ! -f $(TOOL_DIR)/"alloy4.jar"; then \
		echo "[ERROR] Missing $(TOOL_DIR)/alloy4.jar."; false; \
	fi
	find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) | xargs -L1 $(CLAFER)
	@if test ! -f $(TOOL_DIR)/"XsdCheck.class"; then \
		echo "[ERROR] Missing $(TOOL_DIR)/XsdCheck.class."; false; \
	fi
	find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) | xargs -L1 $(CLAFER) -m=xml
	find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) | xargs -L1 $(CLAFER) -m=clafer

clean:
	$(MAKE) -C $(SUITE_DIR) clean
	find . -type f -name '*~' -print0 | xargs -0 rm -f