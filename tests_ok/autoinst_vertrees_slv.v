
module autoinst_vertrees_slv
  (/*AUTOARG*/
   // Outputs
   i2c_mst_data, i2c_read, i2c_slv_scl_out, i2c_slv_sda_out, i2c_spc_scl_state, i2c_start,
   i2c_strobe, slv_bit_st, slv_put, i2c_spc_scl_fall, i2c_spc_sda_state, i2c_spc_start,
   i2c_spc_stop,
   // Inputs
   ck_ref, i2c_slv_data, i2c_slv_scl_in, i2c_slv_sda_in, r_i2c_spc_scl_low, rpt_hold, rpt_sda,
   rst_ref, test_mode
   );
   
   input        ck_ref; // To u_spc of i2c_slv_pin_ctrl.v, ...
   input [7:0]  i2c_slv_data; // To u_misc of ddc_slv_misc.v
   input        i2c_slv_scl_in; // To u_spc of i2c_slv_pin_ctrl.v
   input        i2c_slv_sda_in; // To u_spc of i2c_slv_pin_ctrl.v
   input [4:0]  r_i2c_spc_scl_low; // To u_spc of i2c_slv_pin_ctrl.v
   input        rpt_hold; // To u_misc of ddc_slv_misc.v
   input        rpt_sda; // To u_misc of ddc_slv_misc.v
   input        rst_ref; // To u_spc of i2c_slv_pin_ctrl.v, ...
   input        test_mode; // To u_spc of i2c_slv_pin_ctrl.v
   
   output [7:0] i2c_mst_data; // From u_misc of ddc_slv_misc.v
   output       i2c_read; // From u_misc of ddc_slv_misc.v
   output       i2c_slv_scl_out; // From u_spc of i2c_slv_pin_ctrl.v
   output       i2c_slv_sda_out; // From u_spc of i2c_slv_pin_ctrl.v
   output       i2c_spc_scl_state; // From u_spc of i2c_slv_pin_ctrl.v
   output       i2c_start; // From u_misc of ddc_slv_misc.v
   output       i2c_strobe; // From u_misc of ddc_slv_misc.v
   output       slv_bit_st; // From u_misc of ddc_slv_misc.v
   output       slv_put; // From u_misc of ddc_slv_misc.v
   output       i2c_spc_scl_fall; // From u_spc of i2c_slv_pin_ctrl.v
   output       i2c_spc_sda_state; // From u_spc of i2c_slv_pin_ctrl.v
   output       i2c_spc_start; // From u_spc of i2c_slv_pin_ctrl.v
   output       i2c_spc_stop;           // From u_spc of i2c_slv_pin_ctrl.v
   
endmodule // ddc_slv
