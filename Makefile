D=/home/mac/new_webpage/src/data
S=/home/mac/new_webpage/src
# the directory where the .elc files will be installed
XEMACS  = xemacs
EMACS   = emacs
ELC	= -batch -f batch-byte-compile

uuencoded_verilog-mode : make_log.pl verilog-mode.el README
	make_log.pl	

local:  verilog-mode.el
	cp verilog-mode.el /usr/local/lib/xemacs/site-lisp/verilog-mode.el
	$(XEMACS) $(ELC) $<
	mv verilog-mode.elc /usr/local/lib/xemacs/site-lisp/verilog-mode.elc
	cp verilog-mode.el /usr/local/share/emacs/site-lisp/verilog-mode.el
	$(EMACS) $(ELC) $<
	mv verilog-mode.elc /usr/local/share/emacs/site-lisp/verilog-mode.elc

install : $(D)/uuencoded_verilog-mode $(D)/emacs-version.h $(S)/ChangeLog.txt

$(D)/uuencoded_verilog-mode : uuencoded_verilog-mode
	cp $? $@
$(D)/emacs-version.h : emacs-version.h
	cp $? $@
	touch $(S)/verilog-mode.html
$(S)/ChangeLog.txt : ChangeLog.txt
	cp $? $@

