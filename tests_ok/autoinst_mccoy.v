module top
  
  // no-connecting unused outputs of an interface and tying only inputs to gnd.
  
  // Requested:
  //
  //  /* xx AUTO_TEMPLATE (
  //.TWI_\(.*\) @"(vl-dir (input)"    ({@"vl-width"{1'b0}}),
  //.TWI_\(.*\) @"(vl-dir (output)"    (),
  //);
  //   */
  
  /* xx AUTO_TEMPLATE (
   .TWI_\(.*\) (@"(if (equal vl-dir \\"output\\") \\"\\" (concat vl-width \\"'b0\\"))"),
   );
   */
  
  xx  XX (/*AUTOINST*/
          // Outputs
          .TWI_qb                       (),                      // Templated
          // Inputs
          .clk                          (clk),
          .TWI_ia                       (1'b0),                  // Templated
          .TWI_iw                       (16'b0));                // Templated
endmodule

module xx
  (input clk,
   
   input        TWI_ia,
   input [15:0] TWI_iw,
   output       TWI_qb);
endmodule
