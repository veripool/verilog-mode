
module autoinst_signed_fubar
  (
   input signed [1:0]  an_input,
   output signed [1:0] an_output
   output signed [1:0] another_output
   );
   
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg signed [1:0] an_output;
   reg signed [1:0] another_output;
   // End of automatics
   
endmodule
