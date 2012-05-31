// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by brad Dobbie.

module mod;
   submod #
     (.VEC_W(8),
      .IDX_W($clog2(VEC_W)))
   submod
     (/*AUTOINST*/);
endmodule

module submod (/*AUTOARG*/);
   parameter VEC_W = 32;
   parameter IDX_W = $clog2(VEC_W);
   input  [VEC_W-1:0]   vec;
   output [IDX_W-1:0]   idx;
endmodule

// Local Variables:
// verilog-auto-inst-param-value:t
// End:
