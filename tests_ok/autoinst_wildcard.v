module autoinst_wildcard;
   
   /*AUTOOUTPUT*/
   
   // Newline between AUTO_TEMPLATE and ( gave a templated line number bug
   /* autoinst_wildcard_sub AUTO_TEMPLATE
    (
    .sd0_clk    (sd_clk),
    .sd0_dqm\(.*\)_l    (c@_sd_dqm_[\1]),
    .sd0_ba\([0-9]+\)   (c@_sd_ba[\1]),
    .sd0_adrs@  (c@_sd_adrs[\1]),
    .ics@               (c@_ics[\1]),
    ); */
   
   /*AUTOOUTPUT*/
   
   autoinst_wildcard_sub sub0
     (/*AUTOINST*/
      // Inouts
      .sd_ras_                          (sd_ras_),
      .sd0_dqm7_l                       (c0_sd_dqm_[7]),         // Templated 9
      .sd0_dqm6_l                       (c0_sd_dqm_[6]),         // Templated 9
      .sd0_dqm5_l                       (c0_sd_dqm_[5]),         // Templated 9
      .sd0_dqm4_l                       (c0_sd_dqm_[4]),         // Templated 9
      .sd0_dqm3_l                       (c0_sd_dqm_[3]),         // Templated 9
      .sd0_dqm2_l                       (c0_sd_dqm_[2]),         // Templated 9
      .sd0_dqm1_l                       (c0_sd_dqm_[1]),         // Templated 9
      .sd0_dqm0_l                       (c0_sd_dqm_[0]),         // Templated 9
      .sd0_ba1                          (c0_sd_ba[1]),           // Templated 10
      .sd0_ba0                          (c0_sd_ba[0]),           // Templated 10
      .sd0_adrs11                       (c0_sd_adrs[11]),        // Templated 11
      .sd0_adrs10                       (c0_sd_adrs[10]),        // Templated 11
      .sd0_adrs9                        (c0_sd_adrs[9]),         // Templated 11
      .sd0_adrs8                        (c0_sd_adrs[8]),         // Templated 11
      .sd0_adrs7                        (c0_sd_adrs[7]),         // Templated 11
      .sd0_adrs6                        (c0_sd_adrs[6]),         // Templated 11
      .sd0_adrs5                        (c0_sd_adrs[5]),         // Templated 11
      .sd0_adrs4                        (c0_sd_adrs[4]),         // Templated 11
      .sd0_adrs3                        (c0_sd_adrs[3]),         // Templated 11
      .sd0_adrs2                        (c0_sd_adrs[2]),         // Templated 11
      .sd0_adrs1                        (c0_sd_adrs[1]),         // Templated 11
      .sd0_adrs0                        (c0_sd_adrs[0]),         // Templated 11
      .sd0_clk                          (sd_clk));               // Templated 8
   
endmodule

// Local Variables:
// verilog-auto-inst-template-numbers: t
// End:
