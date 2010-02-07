module ex_output_every (/*AUTOARG*/
                        // Outputs
                        sub1_out_pixel
                        )
  
  /*AUTOOUTPUT*/
  // Beginning of automatic outputs (from unused autoinst outputs)
  output                           pixel24_t sub1_out_pixel;            // From i1 of v2k_typedef_yee_sub1.v
   // End of automatics
   
   v2k_typedef_yee_sub1 i1
     (/*AUTOINST*/
      // Outputs
      .sub1_out_pixel                   (sub1_out_pixel),
      .sub1_to_sub2                     (sub1_to_sub2),
      .sub1_to_sub2_and_top             (sub1_to_sub2_and_top),
      // Inputs
      .sub1_in_pixel                    (sub1_in_pixel),
      .cp                               (cp),
      .reset                            (reset));
   
endmodule

// Local Variables:
// verilog-auto-output-ignore-regexp:"^sub1_to_sub2"
// End:
