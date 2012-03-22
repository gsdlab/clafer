all:
	# download alloy binaries
	
	@if test ! -f "alloy4.jar"; then \
		echo "[WARNING] Missing alloy4.jar. Downloading..."; false; \
		wget http://alloy.mit.edu/alloy/downloads/alloy4.jar
	fi
	
	@if test ! -f "alloy4.2-rc.jar"; then \
		echo "[WARNING] Missing alloy4.2-rc.jar. Downloading..."; false; \
		wget http://alloy.mit.edu/alloy/downloads/alloy4.2-rc.jar
	fi
	
	javac XsdCheck.java

clean:
	find . -type f -name '*.class' -print0 | xargs -0 rm -f