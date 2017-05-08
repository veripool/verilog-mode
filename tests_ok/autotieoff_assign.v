module autotieoff_signed (/*AUTOARG*/
                          // Outputs
                          ExtraOut, SubOut, active_low_l, ignored_by_regexp
                          );
   
   output [2:0] ExtraOut;
   output [2:0] SubOut;
   output [3:0] active_low_l;
   output [3:0] ignored_by_regexp;
   
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   assign ExtraOut = 3'h0;
   assign SubOut = 3'h0;
   assign active_low_l = 4'h0;
   assign ignored_by_regexp = 4'h0;
   // End of automatics
   
endmodule

module sub;
   input  SubIn;
   output SubOut;
endmodule

// Local Variables:
// verilog-auto-tieoff-declaration: "assign"
// End:
