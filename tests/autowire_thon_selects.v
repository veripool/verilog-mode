module foo
  (/*AUTOARG*/);

   /*AUTOOUTPUTEVERY*/

   /*AUTOWIRE*/


   // Check that if aa is connected differently in a input, it doesn't make conflicts.

   autoinst_signed_fubar2 inst
     (
      // Outputs
      .an_output2			(hi.ear.ial),
      .another_output2			(aa[FOO:0]),
      // Inputs
      .an_input2			(an_input2[1:0])
      /*AUTOINST*/);

   autoinst_signed_fubar2 instx
     (
      // Outputs
      .an_output2			(hi.ear.ial),
      // Inputs
      .an_input2			(an_input2[1:0]),
      .another_output2			(aa[Y:X]),
      /*AUTOINST*/);

endmodule
