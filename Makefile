D=/home/mac/external_webpage/src/data
S=/home/mac/external_webpage/src
uuencoded_verilog-mode : make_log.pl verilog-mode.el
	make_log.pl	

install : $(D)/uuencoded_verilog-mode $(D)/emacs-version.h $(S)/ChangeLog.txt

$(D)/uuencoded_verilog-mode : uuencoded_verilog-mode
	cp $? $@
$(D)/emacs-version.h : emacs-version.h
	cp $? $@
	touch $(S)/verilog-mode.html
$(S)/ChangeLog.txt : ChangeLog.txt
	cp $? $@

