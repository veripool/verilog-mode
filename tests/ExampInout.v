        module InstModule (inout io);
        endmodule

        module ExampInout (
           /*AUTOINOUT*/
           // Beginning of automatic inouts (from unused autoinst inouts)
           inout           io                     // To/From instName of InstModule.v
           // End of automatics
           );
           InstModule instName
             (/*AUTOINST*/
              // Inouts
              .io                       (io));
        endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
