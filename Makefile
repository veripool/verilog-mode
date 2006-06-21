S=/home/mac/development/www.verilog.com/src/
D=$(S)data
F=/home/mac/external_webpage/src/verilog.com/ftp
# the directory where the .elc files will be installed
XEMACS  = xemacs
XEMACS_DEST = /usr/local/lib/xemacs/xemacs-packages/lisp/prog-modes/
EMACS   = emacs
EMACS_DEST = /usr/share/emacs/site-lisp/
ELC	= -batch -q -l verilog-mode.el -f batch-byte-compile

release : dirs install
install : dirs test $(D)/mmencoded_verilog-mode $(D)/emacs-version.h\
	$(S)ChangeLog.txt email $(S)bits/verilog-mode.el local \
#	ftp  
	@echo Installation up to date
dirs:	
	@mkdir -p .timestamps
test:	.timestamps/test
.timestamps/test: x/verilog-mode.elc e/verilog-mode.elc mmencoded_verilog-mode verilog.info 0test.el
	$(MAKE) test_batch
	$(MAKE) test_emacs
	$(MAKE) test_xemacs
	@touch $@

test_emacs:
	$(EMACS)  --batch -q -l e/verilog-mode.elc -l 0test.el
test_xemacs:
	$(XEMACS) --batch -q -l x/verilog-mode.elc -l 0test.el
test_batch:
	./batch_test.pl

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
	./make_log.pl	

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


