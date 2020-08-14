module autoinst_paramover_sub (/*AUTOARG*/
                               // Inouts
                               a, b
                               );
   
   //======================================================================
   // Inputs/Outputs
   //======================================================================
   
   parameter       bitsa;
   parameter       bitsb;
   
   inout [bitsa:0] a; // SDRAM Channel 0 Row Address Strobe
   inout [bitsb:0] b;         // SDRAM Channel 0 Row Address Strobe
   
endmodule
