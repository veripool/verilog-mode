        module InstModule (o,i);
           output [31:0] o;
           input i;
           wire [31:0] o = {32{i}};
        endmodule

        module ExampWire (i);
           input i;
           /*AUTOWIRE*/
           // Beginning of automatic wires (for undeclared instantiated-module outputs)
           wire [31:0]     o;                      // From instName of InstModule.v
           // End of automatics
           InstModule instName
             (/*AUTOINST*/
              // Outputs
              .o                        (o[31:0]),
              // Inputs
              .i                        (i));
        endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
