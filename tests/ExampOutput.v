        module InstModule (output o);
        endmodule

        module ExampOutput
           (/*AUTOOUTPUT*/
           // Beginning of automatic outputs (from unused autoinst outputs)
           output          o                       // From instName of InstModule.v
           // End of automatics
            );
           InstModule instName
             (/*AUTOINST*/
              // Outputs
              .o                        (o));
        endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
