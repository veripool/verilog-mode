module autoinst_signed
  (/*AUTOARG*/
   // Outputs
   another_output2, another_output, an_outputpre, an_output2
   );

   /*AUTOOUTPUTEVERY*/
   // Beginning of automatic outputs (every signal)
   output [1:0]		an_output2;		// From u_fubar2 of autoinst_signed_fubar2.v
   output signed [1:0]	an_outputpre;		// From u_fubar of autoinst_signed_fubar.v
   output signed [1:0]	another_output;		// From u_fubar of autoinst_signed_fubar.v
   output [1:0]		another_output2;	// From u_fubar2 of autoinst_signed_fubar2.v
   // End of automatics

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [1:0]		an_output2;		// From u_fubar2 of autoinst_signed_fubar2.v
   wire signed [1:0]	an_outputpre;		// From u_fubar of autoinst_signed_fubar.v
   wire signed [1:0]	another_output;		// From u_fubar of autoinst_signed_fubar.v
   wire [1:0]		another_output2;	// From u_fubar2 of autoinst_signed_fubar2.v
   // End of automatics

   autoinst_signed_fubar u_fubar
     (
      // Outputs
      .an_output			(an_outputpre[1:0]),
      .plover (plump),
      /*AUTOINST*/
      // Outputs
      .another_output			(another_output[1:0]),
      // Inputs
      .an_input				(an_input[1:0]));

   autoinst_signed_fubar2 u_fubar2
     (
      /*AUTOINST*/
      // Outputs
      .an_output2			(an_output2[1:0]),
      .another_output2			(another_output2[1:0]),
      // Inputs
      .an_input2			(an_input2[1:0]));

endmodule
