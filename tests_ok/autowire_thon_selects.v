module foo
  (/*AUTOARG*/
   // Outputs
   aa
   );
   
   /*AUTOOUTPUTEVERY*/
   // Beginning of automatic outputs (every signal)
   output [Y:X] aa; // From inst of autoinst_signed_fubar2.v, ..., Couldn't Merge
   // End of automatics
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [Y:X]   aa;                     // From inst of autoinst_signed_fubar2.v, ..., Couldn't Merge
   // End of automatics
   
   
   // Check that if aa is connected differently in a input, it doesn't make conflicts.
   
   autoinst_signed_fubar2 inst
     (
      // Outputs
      .an_output2                       (hi.ear.ial),
      .another_output2                  (aa[FOO:0]),
      // Inputs
      .an_input2                        (an_input2[1:0])
      /*AUTOINST*/);
   
   autoinst_signed_fubar2 instx
     (
      // Outputs
      .an_output2                       (hi.ear.ial),
      // Inputs
      .an_input2                        (an_input2[1:0]),
      .another_output2                  (aa[Y:X]),
      /*AUTOINST*/);
   
endmodule
