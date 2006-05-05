module io1_sub(
	       /*AUTOARG*/);

   /*AUTOINPUT*/

   /*AUTOINOUT*/

   /*AUTOOUTPUT*/

   /* inst AUTO_TEMPLATE (
    .lower_inb		(1'b1),
    )*/


   instio instio (/*AUTOINST*/);

endmodule

module instio (/*AUTOARG*/);

   input lower_ina;
   inout lower_io;
   output lower_out;

   wire   lower_out = lower_ina | lower_io;

endmodule

