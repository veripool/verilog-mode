
module autoinst_signed_fubar2
  (
   input [1:0]  an_input2,
   output [1:0] an_output2
   output [1:0] another_output2
   );
   
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [1:0] an_output2;
   reg [1:0] another_output2;
   // End of automatics
   
endmodule
