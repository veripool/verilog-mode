module autoinst_vertrees
  (/*AUTOARG*/
   // Outputs
   slv_b_put, slv_b_bit_st, slv_a_put, slv_a_bit_st, i2c_b_strobe, i2c_b_start, i2c_b_spc_stop,
   i2c_b_spc_start, i2c_b_spc_sda_state, i2c_b_spc_scl_state, i2c_b_spc_scl_fall, i2c_b_slv_sda_out,
   i2c_b_slv_scl_out, i2c_b_read, i2c_b_mst_data, i2c_a_strobe, i2c_a_start, i2c_a_spc_stop,
   i2c_a_spc_start, i2c_a_spc_sda_state, i2c_a_spc_scl_state, i2c_a_spc_scl_fall, i2c_a_slv_sda_out,
   i2c_a_slv_scl_out, i2c_a_read, i2c_a_mst_data,
   // Inputs
   test_mode, rst_ref, rpt_b_sda, rpt_b_hold, rpt_a_sda, rpt_a_hold, r_i2c_spc_scl_low,
   i2c_b_slv_sda_in, i2c_b_slv_scl_in, i2c_b_slv_data, i2c_a_slv_sda_in, i2c_a_slv_scl_in,
   i2c_a_slv_data, ck_ref
   );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input       ck_ref; // To u_slv_a of autoinst_vertrees_slv.v, ...
   input       i2c_a_slv_data; // To u_slv_a of autoinst_vertrees_slv.v
   input       i2c_a_slv_scl_in; // To u_slv_a of autoinst_vertrees_slv.v
   input       i2c_a_slv_sda_in; // To u_slv_a of autoinst_vertrees_slv.v
   input       i2c_b_slv_data; // To u_slv_b of autoinst_vertrees_slv.v
   input       i2c_b_slv_scl_in; // To u_slv_b of autoinst_vertrees_slv.v
   input       i2c_b_slv_sda_in; // To u_slv_b of autoinst_vertrees_slv.v
   input [4:0] r_i2c_spc_scl_low; // To u_slv_a of autoinst_vertrees_slv.v, ...
   input       rpt_a_hold; // To u_slv_a of autoinst_vertrees_slv.v
   input       rpt_a_sda; // To u_slv_a of autoinst_vertrees_slv.v
   input       rpt_b_hold; // To u_slv_b of autoinst_vertrees_slv.v
   input       rpt_b_sda; // To u_slv_b of autoinst_vertrees_slv.v
   input       rst_ref; // To u_slv_a of autoinst_vertrees_slv.v, ...
   input       test_mode; // To u_slv_a of autoinst_vertrees_slv.v, ...
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output      i2c_a_mst_data; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_read; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_slv_scl_out; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_slv_sda_out; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_spc_scl_fall; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_spc_scl_state; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_spc_sda_state; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_spc_start; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_spc_stop; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_start; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_a_strobe; // From u_slv_a of autoinst_vertrees_slv.v
   output      i2c_b_mst_data; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_read; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_slv_scl_out; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_slv_sda_out; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_spc_scl_fall; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_spc_scl_state; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_spc_sda_state; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_spc_start; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_spc_stop; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_start; // From u_slv_b of autoinst_vertrees_slv.v
   output      i2c_b_strobe; // From u_slv_b of autoinst_vertrees_slv.v
   output      slv_a_bit_st; // From u_slv_a of autoinst_vertrees_slv.v
   output      slv_a_put; // From u_slv_a of autoinst_vertrees_slv.v
   output      slv_b_bit_st; // From u_slv_b of autoinst_vertrees_slv.v
   output      slv_b_put;               // From u_slv_b of autoinst_vertrees_slv.v
   // End of automatics
   
   /*AUTOWIRE*/
   
   /*
    autoinst_vertrees_slv AUTO_TEMPLATE "u_slv_\([a-z]\)"
    (.i2c_\(.*\) (i2c_@_\1),
    .slv_\(.*\) (slv_@_\1),
    .rpt_\(.*\) (rpt_@_\1),
    )
    */
   autoinst_vertrees_slv u_slv_a
     (/*AUTOINST*/
      // Outputs
      .i2c_mst_data                     (i2c_a_mst_data),        // Templated
      .i2c_read                         (i2c_a_read),            // Templated
      .i2c_slv_scl_out                  (i2c_a_slv_scl_out),     // Templated
      .i2c_slv_sda_out                  (i2c_a_slv_sda_out),     // Templated
      .i2c_spc_scl_state                        (i2c_a_spc_scl_state),   // Templated
      .i2c_start                                (i2c_a_start),           // Templated
      .i2c_strobe                       (i2c_a_strobe),          // Templated
      .slv_bit_st                       (slv_a_bit_st),          // Templated
      .slv_put                          (slv_a_put),             // Templated
      .i2c_spc_scl_fall                 (i2c_a_spc_scl_fall),    // Templated
      .i2c_spc_sda_state                        (i2c_a_spc_sda_state),   // Templated
      .i2c_spc_start                    (i2c_a_spc_start),       // Templated
      .i2c_spc_stop                     (i2c_a_spc_stop),        // Templated
      // Inputs
      .ck_ref                           (ck_ref),
      .i2c_slv_data                     (i2c_a_slv_data),        // Templated
      .i2c_slv_scl_in                   (i2c_a_slv_scl_in),      // Templated
      .i2c_slv_sda_in                   (i2c_a_slv_sda_in),      // Templated
      .r_i2c_spc_scl_low                        (r_i2c_spc_scl_low[4:0]),
      .rpt_hold                         (rpt_a_hold),            // Templated
      .rpt_sda                          (rpt_a_sda),             // Templated
      .rst_ref                          (rst_ref),
      .test_mode                                (test_mode));
   
   autoinst_vertrees_slv u_slv_b
     (/*AUTOINST*/
      // Outputs
      .i2c_mst_data                     (i2c_b_mst_data),        // Templated
      .i2c_read                         (i2c_b_read),            // Templated
      .i2c_slv_scl_out                  (i2c_b_slv_scl_out),     // Templated
      .i2c_slv_sda_out                  (i2c_b_slv_sda_out),     // Templated
      .i2c_spc_scl_state                        (i2c_b_spc_scl_state),   // Templated
      .i2c_start                                (i2c_b_start),           // Templated
      .i2c_strobe                       (i2c_b_strobe),          // Templated
      .slv_bit_st                       (slv_b_bit_st),          // Templated
      .slv_put                          (slv_b_put),             // Templated
      .i2c_spc_scl_fall                 (i2c_b_spc_scl_fall),    // Templated
      .i2c_spc_sda_state                        (i2c_b_spc_sda_state),   // Templated
      .i2c_spc_start                    (i2c_b_spc_start),       // Templated
      .i2c_spc_stop                     (i2c_b_spc_stop),        // Templated
      // Inputs
      .ck_ref                           (ck_ref),
      .i2c_slv_data                     (i2c_b_slv_data),        // Templated
      .i2c_slv_scl_in                   (i2c_b_slv_scl_in),      // Templated
      .i2c_slv_sda_in                   (i2c_b_slv_sda_in),      // Templated
      .r_i2c_spc_scl_low                        (r_i2c_spc_scl_low[4:0]),
      .rpt_hold                         (rpt_b_hold),            // Templated
      .rpt_sda                          (rpt_b_sda),             // Templated
      .rst_ref                          (rst_ref),
      .test_mode                                (test_mode));
   
endmodule // ddc
