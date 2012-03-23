UNAME := $(shell uname | tr "A-Z" "a-z")


ifeq ($(UNAME), darwin)
        WGET_COMMAND :=  curl -O
else
	WGET_COMMAND := wget
endif




all:
	@if test ! -f "alloy4.jar"; then \
		echo "[WARNING] Missing alloy4.jar. Downloading...";  \
		$(WGET_COMMAND) http://alloy.mit.edu/alloy/downloads/alloy4.jar; \
	fi
	@if test ! -f "alloy4.2-rc.jar"; then \
		echo "[WARNING] Missing alloy4.2-rc.jar. Downloading...";  \
		$(WGET_COMMAND) http://alloy.mit.edu/alloy/downloads/alloy4.2-rc.jar; \
	fi
	javac XsdCheck.java
clean:
	find . -type f -name '*.class' -print0 | xargs -0 rm -f