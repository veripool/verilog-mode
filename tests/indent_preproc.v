

aa;
`__FILE__
  `__LINE__
    `celldefine
      `end_keywords
	`resetall
	  `unconnected_drive
	    `undefineall

`ifdef AA
`else
`endif
`ifndef AA
`elsif FOO
`endif

	      `begin_keywords "FOO"
`undef FOO

`line 2 "xx" 2
`include "YY"
`include <YY>
`pragma endofline
`timescale 10ns/10ps
`define foo bar
