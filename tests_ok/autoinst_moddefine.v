// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008-2008 by Wilson Snyder.

module autoinst_moddefine (/*AUTOARG*/);
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire q;                      // From `SUBNAME_B of `SUBMOD_A.v, ...
   // End of automatics
   
`define SUBMOD_A submod_mod
`define SUBNAME_B  subname_b
   
   `SUBMOD_A `SUBNAME_B
     (/*AUTOINST*/
      // Outputs
      .q                                (q),
      // Inputs
      .a                                (a));
   
   `SUBMOD_UNDEFED subundefed
     (/*AUTOINST*/
      // Outputs
      .q                                (q));
   
   submod_decl_from_def subundefed
     (/*AUTOINST*/
      // Outputs
      .q                                (q));
   
endmodule

module submod_mod (/*AUTOARG*/
                   // Outputs
                   q,
                   // Inputs
                   a
                   );
   input  a;
   output q;
endmodule

module SUBMOD_UNDEFED (/*AUTOARG*/
                       // Outputs
                       q
                       );
   output q;
endmodule

`define SUBMOD_DECL submod_decl_from_def
module `SUBMOD_DECL (/*AUTOARG*/
                     // Outputs
                     q
                     );
   output q;
endmodule

// Local Variables:
// verilog-auto-read-includes:t
// End:
