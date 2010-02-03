S=/home/mac/development/www.verilog.com/src/
D=$(S)data
F=/home/mac/external_webpage/src/verilog.com/ftp
# the directory where the .elc files will be installed
XEMACS  = xemacs
XEMACS_DEST = /usr/local/lib/xemacs/xemacs-packages/lisp/prog-modes/
EMACS   = emacs
EMACS_DEST = /usr/local/share/emacs/site-lisp/
ELC	= -batch -q -l verilog-mode.el -f batch-byte-compile
MAKECHANGELOG = perl makechangelog

release : dirs install
install : dirs ChangeLog test $(D)/mmencoded_verilog-mode $(D)/emacs-version.h\
	$(S)ChangeLog.txt email $(S)bits/verilog-mode.el local \
#	ftp  
	@echo Installation up to date
dirs:	
	@mkdir -p .timestamps
test:	.timestamps/test
.timestamps/test: x/verilog-mode.elc e/verilog-mode.elc mmencoded_verilog-mode verilog.info 0test.el
	$(MAKE) test_batch
	$(MAKE) test_errors
	$(MAKE) test_emacs
	$(MAKE) test_xemacs
	@touch $@

test_emacs: e/verilog-mode.elc
	@echo
	@echo == test_emacs
	time $(EMACS)  --batch -q -l e/verilog-mode.elc -l 0test.el
test_xemacs: x/verilog-mode.elc
	@echo
	@echo == test_xemacs
	time $(XEMACS) --batch -q -l x/verilog-mode.elc -l 0test.el
test_errors:
	@echo
	@echo == test_errors
	@echo emit a bunch of error messages that Emacs should
	@echo "recognize if you type C-x \` and take you to the correct line of error_file.v"
	@echo "Warning: code located there (error_file.v line 9) is dangerous"
	@echo "(W1800) error_file.v 21: Problems"
	@echo "f*E,1364 (error_file.v,2) Issues"
	@echo "Error: code located here (error_file.v line 8) is fatal"
	@echo "ERROR  : error_file.v, line 1: erroneous"
	@echo "INFO  : error_file.v, line 7: informational"
	@echo "WARNING : error_file.v, line 6: curious"
	@echo "In file error_file.v line 5:"
	@echo "a"
	@echo "b"
	@echo "Failure was obsevred"
	@echo la di da
	@echo syntax error: problems
	@echo error_file.v 7: here is where they are
test_batch:
	@echo == test_batch
	time ./batch_test.pl

local:	.timestamps/local
.timestamps/local:  verilog-mode.el
	cp verilog-mode.el $(XEMACS_DEST)verilog-mode.el
	$(XEMACS) $(ELC) $(XEMACS_DEST)verilog-mode.el
	cp verilog-mode.el $(EMACS_DEST)verilog-mode.el
	$(EMACS) $(ELC) $(EMACS_DEST)verilog-mode.el
	@touch $@

ftp:	.timestamps/ftp
.timestamps/ftp:	$(F) mmencoded_verilog-mode verilog-mode.el README
	cp mmencoded_verilog-mode $(F)
	cp verilog-mode.el $(F)
	cp README $(F)/.message
	@touch $@

$(F):
	mkdir $(F)

ChangeLog.txt mmencoded_verilog-mode emacs-version.h : make_log.pl verilog-mode.el README
ifneq ($(VERILOGMODE_SKIP_MAKELOG),1)
	./make_log.pl	
endif

ChangeLog : verilog-mode.el makechangelog
	$(MAKECHANGELOG) --svn verilog-mode.el > $@

email:	.timestamps/email
.timestamps/email: mmencoded_verilog-mode
	./make_mail.pl
	@touch $@

$(D)/mmencoded_verilog-mode : mmencoded_verilog-mode
	cp $? $@
$(D)/emacs-version.h : emacs-version.h
	cp $? $@
	touch $(S)verilog-mode.html
$(S)ChangeLog.txt : ChangeLog.txt
	cp $? $@
$(S)bits/verilog-mode.el : verilog-mode.el
	cp $? $@

x/verilog-mode.elc : verilog-mode.el
	rm -rf x
	mkdir x
	cp verilog-mode.el x/verilog-mode.el
	$(XEMACS) $(ELC) x/verilog-mode.el

e/verilog-mode.elc : verilog-mode.el
	-rm -rf e
	-mkdir e
	cp verilog-mode.el e/verilog-mode.el
	$(EMACS) $(ELC) e/verilog-mode.el

verilog.info : verilog.texinfo
	makeinfo verilog.texinfo > verilog.info

######################################################################
# GNU BZR version
#  --- Note gnutrunk needs to be a symlink to a emacs/trunk bazaar checkout

.PHONY: gnu-update gnu-update-trunk
gnu-update: gnu-update-trunk
gnu-update-trunk:
	cd gnutrunk && bzr update

.PHONY: gnu-diff-trunk gnu-diff
gnu-diff: gnu-diff-trunk
gnu-diff-trunk: gnu-update-trunk verilog-mode-tognu.el
	diff -c gnutrunk/lisp/progmodes/verilog-mode.el verilog-mode-tognu.el 
patch-file: gnu-update-head verilog-mode-tognu.el
	diff -c gnutrunk/lisp/progmodes/verilog-mode.el verilog-mode-tognu.el > patch-file

verilog-mode-tognu.el: verilog-mode.el Makefile
	cat verilog-mode.el \
	 | sed 's/ *\$$Id:.*//g' \
	 | sed 's/(substring.*\$$\$$Revision: \([0-9]*\).*$$/"\1"/g' \
	 | sed 's/(substring.*\$$\$$Date: \(....-..-..\).*).*$$/"\1-GNU"/g' \
	 | sed 's/verilog-mode-release-emacs nil/verilog-mode-release-emacs t/g' \
	 > verilog-mode-tognu.el

######################################################################
# Clean

clean::
	/bin/rm -rf .timestamps e/*.elc x/*.elc


