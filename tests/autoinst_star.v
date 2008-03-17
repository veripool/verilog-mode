module io1_sub (/*AUTOARG*/);

   /*AUTOWIRE*/

   autoinst_lopaz_srpad MD31_pad
     (.*,
      .foo (touch_this_not_my_pretty));

   /* autoinst_lopaz_srpad AUTO_TEMPLATE (
    ); */

   autoinst_lopaz_srpad MD31_pad
     (.*);

  /* autoinst_lopaz_srpad AUTO_TEMPLATE (
      .pin	(templated));
    */

   autoinst_lopaz_srpad MD31_pad
     (.*);

   // And .name with auto inst
   autoinst_lopaz_srpad MD31_pad22
     (.pin,
      .clk,
      /*AUTOINST*/);

   always @(posedge clk) begin
      $display ("This .* shouldn't expand.\n");
   end

endmodule
