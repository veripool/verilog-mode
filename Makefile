uuencoded_verilog-mode : make_log.pl verilog-mode.el
	make_log.pl	
	cvs log verilog-mode.el > l1
	cat l1 | chop_log.pl > log
	cat preamble log uu > $@
	rm l1 log

uu: verilog-mode.el.gz
	uuencode verilog-mode.el.gz < verilog-mode.el.gz > $@

verilog-mode.el.gz : verilog-mode.el
	gzip -c9 verilog-mode.el > $@
