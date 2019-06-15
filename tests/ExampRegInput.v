        module InstModule (input i);
        endmodule

        module ExampRegInput ();
           /*AUTOREGINPUT*/
           // Beginning of automatic reg inputs (for undeclared instantiated-module inputs)
           reg             i;                      // To instName of InstModule.v
           // End of automatics
           InstModule instName
             (/*AUTOINST*/
              // Inputs
              .i                        (i));
        endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
