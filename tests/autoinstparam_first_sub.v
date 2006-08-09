module autoinstparam_first_sub (/*AUTOARG*/
   // Inouts
   a, b
   );

   //======================================================================
   // Inputs/Outputs
   //======================================================================

   localparam IGNORED;
   parameter BITSA;
   parameter BITSB;

   inout [BITSA:0] a;
   inout [BITSB:0] b;

endmodule
