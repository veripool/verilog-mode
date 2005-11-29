module foo
  (/*AUTOARG*/
   // Outputs
   another_output2
   );

   /*AUTOOUTPUTEVERY*/
   // Beginning of automatic outputs (every signal)
   output [1:0]		another_output2;	// From inst of autoinst_signed_fubar2.v
   // End of automatics

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [1:0]		another_output2;	// From inst of autoinst_signed_fubar2.v
   // End of automatics


   /* autoinst_signed_fubar2 AUTO_TEMPLATE (
    .an_output2	(hi.ear.ial),
    );
    */

   autoinst_signed_fubar2 inst
     (
      /*AUTOINST*/
      // Outputs
      .an_output2			(hi.ear.ial),		 // Templated
      .another_output2			(another_output2[1:0]),
      // Inputs
      .an_input2			(an_input2[1:0]));

endmodule
