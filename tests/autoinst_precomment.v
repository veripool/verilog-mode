module autoinst_precomment (
			    why,
			    /*AUTOARG*/
   // Inputs
   nnnot
   );
   input why;
   input nnnot;

   autoinst_wildcard_sub sub0
     (
      .sd_ras_				(foobar_ras_),
      //.sd0_dqm7_l			(dontdome),
      /*AUTOINST*/
      // Inouts
      .sd0_dqm7_l			(sd0_dqm7_l),
      .sd0_dqm6_l			(sd0_dqm6_l),
      .sd0_dqm5_l			(sd0_dqm5_l),
      .sd0_dqm4_l			(sd0_dqm4_l),
      .sd0_dqm3_l			(sd0_dqm3_l),
      .sd0_dqm2_l			(sd0_dqm2_l),
      .sd0_dqm1_l			(sd0_dqm1_l),
      .sd0_dqm0_l			(sd0_dqm0_l),
      .sd0_ba1				(sd0_ba1),
      .sd0_ba0				(sd0_ba0),
      .sd0_adrs11			(sd0_adrs11),
      .sd0_adrs10			(sd0_adrs10),
      .sd0_adrs9			(sd0_adrs9),
      .sd0_adrs8			(sd0_adrs8),
      .sd0_adrs7			(sd0_adrs7),
      .sd0_adrs6			(sd0_adrs6),
      .sd0_adrs5			(sd0_adrs5),
      .sd0_adrs4			(sd0_adrs4),
      .sd0_adrs3			(sd0_adrs3),
      .sd0_adrs2			(sd0_adrs2),
      .sd0_adrs1			(sd0_adrs1),
      .sd0_adrs0			(sd0_adrs0),
      .sd0_clk				(sd0_clk));

endmodule
