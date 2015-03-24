// Julian Gorfajn

`default_nettype none

module top
  (
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output wire o, // From sub of Sub.v
   // End of automatics
   // Beginning of automatic outputs (from unused autoinst outputs)
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input wire  i                        // To sub of Sub.v
   // End of automatics
   );
   
   Sub sub (/*AUTOINST*/
            // Outputs
            .o                          (o),
            // Inputs
            .i                          (i));
endmodule

module Sub (input i, output o);
endmodule

// Local Variables:
// verilog-auto-declare-nettype: "wire"
// End:
