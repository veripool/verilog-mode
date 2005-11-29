module io1_sub(
	       /*AUTOARG*/);

   /* autoinst_lopaz_srpad AUTO_TEMPLATE (
    .pin_in(),
    // Inputs
    .pin_out (),
    ); */

   autoinst_lopaz_srpad i_ctrl
     (/*AUTOINST*/
      // Outputs
      .pin_in				(),			 // Templated
      // Inouts
      .pin				(pin[w-1:0]),
      // Inputs
      .clk				(clk),
      .pin_out				(),			 // Templated
      .pin_outen			(pin_outen));

endmodule
