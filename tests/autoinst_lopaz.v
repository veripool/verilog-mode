module io1_sub(
	       /*AUTOARG*/);

   wire	[42:0]	bscan_data;         // boundary scan stitch
   parameter 	bscan_count = 0;

   assign 	bscan_data[0] = bscan_in;

   /*
    * Emacs template to auto instaniate MD[31:0] pads
    */
   /*
    autoinst_lopaz_srpad AUTO_TEMPLATE (
    .pin(MD[@]),
    .pin_in({SDRAM_DQ_in[@],SDRAM_DQ_in[@]}),
    .pin_out(SDRAM_DQ_out[@]),
    .pin_outen(SDRAM_DQ_outen),
    .sdrmode(SDRAM_single_rate),
    .hw_enb(SDRAM_upper_word_enb),
    .ff_rptr(SDRAM_ddr_inff_sel),
    .ff_wptr(ddr_inff_enbH),
    .clk(data_strobeH),
    .bscan_so(bscan_data[@ + 1]),
    .bscan_si(bscan_data[@]),
    .bscan_shift(BScanShift),
    .bscan_clock(BScanClock),
    .bscan_mode(BScanMode),
    .bscan_update(BScanUpdate),
    .bscan_outen(SDRAM_DQ_bscan_outen),
    );
    */

   autoinst_lopaz_srpad MD31_pad (/*AUTOINST*/);


   /* autoinst_lopaz_srpad AUTO_TEMPLATE (
    .pin(MD[@"num"]),
    );
    */

   /*AUTO_LISP(setq num 1)*/
   autoinst_lopaz_srpad MD31_pad11 (/*AUTOINST*/);

   /* autoinst_lopaz_srpad AUTO_TEMPLATE (
    .pin(MD[@"num"]),
    );
    */

   /*AUTO_LISP(setq num 2)*/
   autoinst_lopaz_srpad MD31_pad11 (/*AUTOINST*/);

endmodule
