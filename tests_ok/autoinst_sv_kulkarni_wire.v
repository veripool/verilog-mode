`timescale 1ns/100ps

module a_h
  #(parameter M=5, N=3)
   ();
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [N-1:0] [M-1:0] a_o1;                  // From Ia of autoinst_sv_kulkarni_base.v
   // End of automatics
   
   autoinst_sv_kulkarni_base
     #(/*AUTOINSTPARAM*/
       // Parameters
       .M                               (M),
       .N                               (N))
   Ia
     (/*AUTOINST*/
      // Outputs
      .a_o1                             (a_o1/*[N-1:0][M-1:0]*/),
      // Inputs
      .a_i1                             (a_i1/*[N-1:0][M-1:0]*/)); // <---- BUG?
   
endmodule
