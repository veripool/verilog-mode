// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008-2008 by Wilson Snyder.

module autoinst_moddefine (/*AUTOARG*/);

   /*AUTOWIRE*/

`define SUBMOD_A submod_mod
`define SUBNAME_B  subname_b

   `SUBMOD_A `SUBNAME_B
     (/*AUTOINST*/);

   `SUBMOD_UNDEFED subundefed
     (/*AUTOINST*/);

   submod_decl_from_def subundefed
     (/*AUTOINST*/);

endmodule

module submod_mod (/*AUTOARG*/);
   input a;
   output q;
endmodule

module SUBMOD_UNDEFED (/*AUTOARG*/);
   output q;
endmodule

`define SUBMOD_DECL submod_decl_from_def
module `SUBMOD_DECL (/*AUTOARG*/);
   output q;
endmodule

// Local Variables:
// verilog-auto-read-includes:t
// End:
