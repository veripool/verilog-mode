module InstModule (input i);
endmodule

module ExampInput (
                   /*AUTOINPUT*/
                   // Beginning of automatic inputs (from unused autoinst inputs)
                   input i                      // To instName of InstModule.v
                   // End of automatics
                   );
   InstModule instName
     (/*AUTOINST*/
      // Inputs
      .i                        (i));
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
