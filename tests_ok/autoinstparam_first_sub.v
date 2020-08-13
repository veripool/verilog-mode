module autoinstparam_first_sub (/*AUTOARG*/
                                // Inouts
                                a, b
                                );
   
   //======================================================================
   // Inputs/Outputs
   //======================================================================
   
   localparam      IGNORED;
   parameter       BITSA;
   parameter       type BITSB_t = bit; // See bug340
   
   inout [BITSA:0] a;
   inout           BITSB_t b;
   
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
