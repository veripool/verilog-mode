module autoinst_paramover (/*AUTOARG*/
   // Inouts
   a, b
   );

   //======================================================================
   // Inputs/Outputs
   //======================================================================

   parameter bitsa = 20;
   parameter bitsb = 20;

   inout [20:0] a;         // SDRAM Channel 0 Row Address Strobe
   inout [20:0] b;         // SDRAM Channel 0 Row Address Strobe

   autoinst_paramover_sub #(bitsa,bitsb ) mod
     (/*AUTOINST*/
      // Inouts
      .a				(a[bitsa:0]),
      .b				(b[bitsb:0]));

endmodule
