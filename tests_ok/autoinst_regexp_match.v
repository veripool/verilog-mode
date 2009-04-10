module autoinst_wildcard;
   
   /*AUTOINOUT*/
   // Beginning of automatic inouts (from unused autoinst inouts)
   inout [0] [9:0] SD_ADRS; // To/From sub0 of autoinst_wildcard_sub.v, ...
   inout [0] [1:0] SD_ADRS1; // To/From sub0 of autoinst_wildcard_sub.v, ...
   inout [0] [1:0] SD_BA; // To/From sub0 of autoinst_wildcard_sub.v, ...
   inout [0] [7:0] SD_DQM_L; // To/From sub0 of autoinst_wildcard_sub.v, ...
   inout           sd0_clk; // To/From sub0 of autoinst_wildcard_sub.v, ...
   inout [0] [9:0] sd_adrs; // To/From sub1 of autoinst_wildcard_sub.v, ...
   inout [0] [1:0] sd_adrs1; // To/From sub1 of autoinst_wildcard_sub.v, ...
   inout [0] [1:0] sd_ba; // To/From sub1 of autoinst_wildcard_sub.v, ...
   inout [0] [7:0] sd_dqm_l; // To/From sub1 of autoinst_wildcard_sub.v, ...
   inout           sd_ras_;             // To/From sub0 of autoinst_wildcard_sub.v, ...
   // End of automatics
   
   /* autoinst_wildcard_sub AUTO_TEMPLATE (
    .sd\([0-9]\)_\(.*\)\([0-9]+\)\(.*\) (@"(uc \\"sd_\2\4[\1][\3]\\")"),
    ); */
   
   /*AUTOOUTPUT*/
   
   autoinst_wildcard_sub sub0
     (/*AUTOINST*/
      // Inouts
      .sd_ras_                          (sd_ras_),
      .sd0_dqm7_l                       (SD_DQM_L[0][7]),        // Templated
      .sd0_dqm6_l                       (SD_DQM_L[0][6]),        // Templated
      .sd0_dqm5_l                       (SD_DQM_L[0][5]),        // Templated
      .sd0_dqm4_l                       (SD_DQM_L[0][4]),        // Templated
      .sd0_dqm3_l                       (SD_DQM_L[0][3]),        // Templated
      .sd0_dqm2_l                       (SD_DQM_L[0][2]),        // Templated
      .sd0_dqm1_l                       (SD_DQM_L[0][1]),        // Templated
      .sd0_dqm0_l                       (SD_DQM_L[0][0]),        // Templated
      .sd0_ba1                          (SD_BA[0][1]),           // Templated
      .sd0_ba0                          (SD_BA[0][0]),           // Templated
      .sd0_adrs11                       (SD_ADRS1[0][1]),        // Templated
      .sd0_adrs10                       (SD_ADRS1[0][0]),        // Templated
      .sd0_adrs9                        (SD_ADRS[0][9]),         // Templated
      .sd0_adrs8                        (SD_ADRS[0][8]),         // Templated
      .sd0_adrs7                        (SD_ADRS[0][7]),         // Templated
      .sd0_adrs6                        (SD_ADRS[0][6]),         // Templated
      .sd0_adrs5                        (SD_ADRS[0][5]),         // Templated
      .sd0_adrs4                        (SD_ADRS[0][4]),         // Templated
      .sd0_adrs3                        (SD_ADRS[0][3]),         // Templated
      .sd0_adrs2                        (SD_ADRS[0][2]),         // Templated
      .sd0_adrs1                        (SD_ADRS[0][1]),         // Templated
      .sd0_adrs0                        (SD_ADRS[0][0]),         // Templated
      .sd0_clk                          (sd0_clk));
   
   /* autoinst_wildcard_sub AUTO_TEMPLATE (
    .sd\([0-9]\)_\(.*\)\([0-9]+\)\(.*\) (sd_\2\4[\1][\3]),
    ); */
   
   /*AUTOOUTPUT*/
   
   autoinst_wildcard_sub sub1
     (/*AUTOINST*/
      // Inouts
      .sd_ras_                          (sd_ras_),
      .sd0_dqm7_l                       (sd_dqm_l[0][7]),        // Templated
      .sd0_dqm6_l                       (sd_dqm_l[0][6]),        // Templated
      .sd0_dqm5_l                       (sd_dqm_l[0][5]),        // Templated
      .sd0_dqm4_l                       (sd_dqm_l[0][4]),        // Templated
      .sd0_dqm3_l                       (sd_dqm_l[0][3]),        // Templated
      .sd0_dqm2_l                       (sd_dqm_l[0][2]),        // Templated
      .sd0_dqm1_l                       (sd_dqm_l[0][1]),        // Templated
      .sd0_dqm0_l                       (sd_dqm_l[0][0]),        // Templated
      .sd0_ba1                          (sd_ba[0][1]),           // Templated
      .sd0_ba0                          (sd_ba[0][0]),           // Templated
      .sd0_adrs11                       (sd_adrs1[0][1]),        // Templated
      .sd0_adrs10                       (sd_adrs1[0][0]),        // Templated
      .sd0_adrs9                        (sd_adrs[0][9]),         // Templated
      .sd0_adrs8                        (sd_adrs[0][8]),         // Templated
      .sd0_adrs7                        (sd_adrs[0][7]),         // Templated
      .sd0_adrs6                        (sd_adrs[0][6]),         // Templated
      .sd0_adrs5                        (sd_adrs[0][5]),         // Templated
      .sd0_adrs4                        (sd_adrs[0][4]),         // Templated
      .sd0_adrs3                        (sd_adrs[0][3]),         // Templated
      .sd0_adrs2                        (sd_adrs[0][2]),         // Templated
      .sd0_adrs1                        (sd_adrs[0][1]),         // Templated
      .sd0_adrs0                        (sd_adrs[0][0]),         // Templated
      .sd0_clk                          (sd0_clk));
   
endmodule

// Local Variables:
// eval:(defun uc (x) (upcase x))
// End:
