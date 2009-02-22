module autoinst_wildcard_sub (/*AUTOARG*/
                              // Inouts
                              sd_ras_, sd0_dqm7_l, sd0_dqm6_l, sd0_dqm5_l, sd0_dqm4_l, sd0_dqm3_l,
                              sd0_dqm2_l, sd0_dqm1_l, sd0_dqm0_l, sd0_ba1, sd0_ba0, sd0_adrs11,
                              sd0_adrs10, sd0_adrs9, sd0_adrs8, sd0_adrs7, sd0_adrs6, sd0_adrs5,
                              sd0_adrs4, sd0_adrs3, sd0_adrs2, sd0_adrs1, sd0_adrs0, sd0_clk
                              );
   
   //======================================================================
   // Inputs/Outputs
   //======================================================================
   
   inout sd_ras_; // SDRAM Channel 0 Row Address Strobe
   inout sd0_dqm7_l; // SDRAM Channel 0 DQM Mask Bits
   inout sd0_dqm6_l;
   inout sd0_dqm5_l;
   inout sd0_dqm4_l;
   inout sd0_dqm3_l;
   inout sd0_dqm2_l;
   inout sd0_dqm1_l;
   inout sd0_dqm0_l;
   inout sd0_ba1;
   inout sd0_ba0;
   inout sd0_adrs11; // SDRAM Channel 0 Address
   inout sd0_adrs10;
   inout sd0_adrs9;
   inout sd0_adrs8;
   inout sd0_adrs7;
   inout sd0_adrs6;
   inout sd0_adrs5;
   inout sd0_adrs4;
   inout sd0_adrs3;
   inout sd0_adrs2;
   inout sd0_adrs1;
   inout sd0_adrs0;
   inout sd0_clk;         // SDRAM Channel 0 Clocks
   
endmodule

// Local Variables:
// fill-column: 79
// End:
