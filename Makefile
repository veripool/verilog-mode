D=/home/mac/external_webpage/src/verilog.com/data
S=/home/mac/external_webpage/src/verilog.com/
F=/home/mac/external_webpage/src/verilog.com/ftp
# the directory where the .elc files will be installed
XEMACS  = xemacs
EMACS   = emacs
ELC	= -batch -f batch-byte-compile

test:	x/verilog-mode.elc e/verilog-mode.elc mmencoded_verilog-mode verilog.info

local:  verilog-mode.el
	cp verilog-mode.el /usr/local/lib/xemacs/site-lisp/verilog-mode.el
	$(XEMACS) $(ELC) /usr/local/lib/xemacs/site-lisp/verilog-mode.el
	cp verilog-mode.el /usr/local/share/emacs/site-lisp/verilog-mode.elc
	$(EMACS) $(ELC) /usr/local/share/emacs/site-lisp/verilog-mode.elc

ftp:	$(F) mmencoded_verilog-mode verilog-mode.el README
	cp mmencoded_verilog-mode $(F)
	cp verilog-mode.el $(F)
	cp README $(F)/.message

$(F):
	mkdir $(F)

install : $(D)/mmencoded_verilog-mode $(D)/emacs-version.h\
	 $(S)ChangeLog.txt local ftp $(S)bits/verilog-mode.el

mmencoded_verilog-mode : make_log.pl verilog-mode.el README
	make_log.pl	

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
	@-mkdir x
	cp verilog-mode.el x/verilog-mode.el
	$(XEMACS) $(ELC) x/verilog-mode.el

e/verilog-mode.elc : verilog-mode.el
	@-mkdir e
	cp verilog-mode.el e/verilog-mode.el
	$(EMACS) $(ELC) e/verilog-mode.el

verilog.info : verilog.texinfo
	makeinfo verilog.texinfo > verilog.info


