WGET_COMMAND := wget
ifeq ($(OS),Windows_NT)
	ifeq ($(shell which wget), which: wget: unkown command)
		mingw-get install msys-wget-bin
	endif
else
	UNAME_S := $(shell uname -s)
	ifeq ($(UNAME_S),Darwin)
		WGET_COMMAND := curl -O
	endif
endif

all:
	@if test ! -f "alloy4.jar"; then \
		echo "[WARNING] Missing alloy4.jar. Downloading...";  \
		$(WGET_COMMAND) http://alloy.mit.edu/alloy/downloads/alloy4.jar; \
	fi

	@if test ! -f "alloy4.2.jar"; then \
		echo "[WARNING] Missing alloy4.2.jar. Downloading...";  \
		$(WGET_COMMAND) http://alloy.mit.edu/alloy/downloads/alloy4.2_2014-05-16.jar; \
		mv alloy4.2_2014-05-16.jar alloy4.2.jar; \
	fi

	javac -source 1.6 -target 1.6 XsdCheck.java
clean:
	find . -type f -name '*.class' -print0 | xargs -0 rm -f