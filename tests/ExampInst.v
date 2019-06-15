        module InstModule (o,i);
           output [31:0] o;
           input i;
           wire [31:0] o = {32{i}};
        endmodule

        module ExampInst (o,i);
           output o;
           input i;
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
