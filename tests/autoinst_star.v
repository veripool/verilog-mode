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

endmodule
