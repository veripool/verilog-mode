
`include "v2k_typedef_yee_inc.v"
module v2k_typedef_yee
  (/*AUTOARG*/
   // Outputs
   sub2_out_pixel, ready, sub1_to_sub2_and_top,
   // Inputs
   sub1_in_pixel, reset, pixel_ff, cp
   );
   
   //-----------------------
   // Output definitions
   //
   output logic_t sub1_to_sub2_and_top; // Explicit output port
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output logic_t ready; // From itest_sub2 of v2k_typedef_yee_sub2.v
   output pixel24_t sub2_out_pixel; // From itest_sub2 of v2k_typedef_yee_sub2.v
   // End of automatics
   
   
   //-----------------------
   // Input definitions
   //
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input  logic_t cp; // To itest_sub1 of v2k_typedef_yee_sub1.v, ...
   input  logic_t pixel24_t pixel_ff; // To itest_sub2 of v2k_typedef_yee_sub2.v
   input  logic_t reset; // To itest_sub1 of v2k_typedef_yee_sub1.v, ...
   input  pixel24_t sub1_in_pixel;              // To itest_sub1 of v2k_typedef_yee_sub1.v
   // End of automatics
   
   
   //-----------------------
   // Wire definitions
   //
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   pixel24_t            sub1_out_pixel;         // From itest_sub1 of v2k_typedef_yee_sub1.v
   logic_t              sub1_to_sub2;           // From itest_sub1 of v2k_typedef_yee_sub1.v
   // End of automatics
   
   
   
   //-----------------------
   // Module instantiations
   //
   v2k_typedef_yee_sub1 itest_sub1
     (/*AUTOINST*/
      // Outputs
      .sub1_out_pixel                   (sub1_out_pixel),
      .sub1_to_sub2                     (sub1_to_sub2),
      .sub1_to_sub2_and_top             (sub1_to_sub2_and_top),
      // Inputs
      .sub1_in_pixel                    (sub1_in_pixel),
      .cp                               (cp),
      .reset                            (reset));
   
   /*v2k_typedef_yee_sub2 AUTO_TEMPLATE (
    .sub2_in_pixel (sub1_out_pixel),
    )
    */
   v2k_typedef_yee_sub2 itest_sub2
     (/*AUTOINST*/
      // Outputs
      .sub2_out_pixel                   (sub2_out_pixel),
      .ready                            (ready),
      // Inputs
      .sub2_in_pixel                    (sub1_out_pixel),        // Templated
      .cp                               (cp),
      .reset                            (reset),
      .sub1_to_sub2                     (sub1_to_sub2),
      .sub1_to_sub2_and_top             (sub1_to_sub2_and_top),
      .pixel_ff                         (pixel_ff));
   
   
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
