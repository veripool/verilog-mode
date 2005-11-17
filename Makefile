S=/home/mac/development/www.verilog.com/src/
D=$(S)data
F=/home/mac/external_webpage/src/verilog.com/ftp
# the directory where the .elc files will be installed
XEMACS  = xemacs
EMACS   = emacs
ELC	= -batch -f batch-byte-compile

release : install
install : test $(D)/mmencoded_verilog-mode $(D)/emacs-version.h\
	 $(S)ChangeLog.txt email $(S)bits/verilog-mode.el local \
	#ftp

test:	x/verilog-mode.elc e/verilog-mode.elc mmencoded_verilog-mode verilog.info

local:  verilog-mode.el
	cp verilog-mode.el /usr/local/lib/xemacs/site-lisp/verilog-mode.el
	$(XEMACS) $(ELC) /usr/local/lib/xemacs/site-lisp/verilog-mode.el
	cp verilog-mode.el /usr/share/emacs/site-lisp/verilog-mode.el
	$(EMACS) $(ELC) /usr/share/emacs/site-lisp/verilog-mode.el

ftp:	$(F) mmencoded_verilog-mode verilog-mode.el README
	cp mmencoded_verilog-mode $(F)
	cp verilog-mode.el $(F)
	cp README $(F)/.message

$(F):
	mkdir $(F)

mmencoded_verilog-mode : make_log.pl verilog-mode.el README
	./make_log.pl	

email: mmencoded_verilog-mode
	./make_mail.pl

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


