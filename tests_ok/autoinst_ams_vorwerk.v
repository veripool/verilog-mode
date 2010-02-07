module autoinst_ams_vorwerk;
   
   latch latch (/*AUTOINST*/
                // Outputs
                .q                      (q),
                // Inputs
                .en                     (en),
                .d                      (d));
   
endmodule

module latch (/*AUTOARG*/
              // Outputs
              q,
              // Inputs
              en, d
              );
   
`ifdef __VAMS_ENABLE__
   output                                                                              (* integer groundSensitivity="gnd "; integer supplySensitivity="vdd "; *) q;
`else
   output    q;
`endif
   
`ifdef __VAMS_ENABLE__
   input                                                                               (* integer groundSensitivity="gnd "; integer supplySensitivity="vdd "; *) en;
`else
   input     en;
`endif
   
`ifdef __VAMS_ENABLE__
   input                                                                              (* integer groundSensitivity="gnd "; integer supplySensitivity="vdd "; *) d;
`else
   input    d;
`endif
   
endmodule
