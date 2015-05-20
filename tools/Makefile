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

all:
	@if test ! -f "alloy4.2.jar"; then \
		echo "[WARNING] Missing alloy4.2.jar. Downloading...";  \
		$(WGET_COMMAND) http://alloy.mit.edu/alloy/downloads/alloy4.2_2015-02-22.jar; \
		mv alloy4.2_2015-02-22.jar alloy4.2.jar; \
	fi

clean:
	find . -type f -name '*.class' -print0 | xargs -0 rm -f
