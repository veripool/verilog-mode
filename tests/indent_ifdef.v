module test(out);
  output out;
`define wow
`define nest_one
`define second_nest
`define nest_two
`ifdef wow
  initial $display("wow is defined");
  `ifdef nest_one
  initial $display("nest_one is defined");
    `ifdef nest_two
  initial $display("nest_two is defined");
    `else
  initial $display("nest_two is not defined");
    `endif
  `else
  initial $display("nest_one is not defined");
  `endif
`else
   initial $display("wow is not defined");
 `ifdef second_nest
   initial $display("second_nest is defined");
 `else
   initial $display("second_nest is not defined");
 `endif
`endif
endmodule


// Local Variables:
// verilog-auto-lineup: all
// verilog-auto-endcomments: t
// verilog-auto-indent-on-newline: t
// verilog-auto-lineup: all
// verilog-auto-newline: nil
// verilog-case-indent: 2
// verilog-highlight-p1800-keywords: nil
// verilog-indent-begin-after-if: t
// verilog-indent-level: 2
// verilog-indent-level-behavioral: 2
// verilog-indent-level-declaration: 2
// verilog-indent-level-directive: 2
// verilog-indent-level-module: 2
// verilog-minimum-comment-distance: 40
// verilog-tab-always-indent: t
// End:
