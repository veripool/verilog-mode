        module InstModule (o,i);
           parameter WIDTH;
           input [WIDTH-1:0] i;
           parameter type OUT_t;
           output OUT_t o;
        endmodule

        module vm_example1;
           /*AUTOOUTPUT*/
           // Beginning of automatic outputs (from unused autoinst outputs)
           output upper_t  o;                      // From instName of InstModule.v
           // End of automatics

           InstModule
             #(.WIDTH(10),
               ,.OUT_t(upper_t))
            instName
             (/*AUTOINST*/
              // Outputs
              .o                        (o),
              // Inputs
              .i                        (i[9:0]));
        endmodule

        // Local Variables:
        // verilog-typedef-regexp: "_t$"
        // verilog-auto-inst-param-value: t
        // End:
