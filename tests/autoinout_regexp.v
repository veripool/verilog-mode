module io1_sub(
	       /*AUTOARG*/);

   /*AUTOINPUT("^s")*/

   /*AUTOINOUT("^s")*/

   /*AUTOOUTPUT("^s")*/

   /* inst AUTO_TEMPLATE (
    .lower_inb		(1'b1),
    )*/


   instio instio (/*AUTOINST*/);

endmodule

module instio (/*AUTOARG*/);

   input lower_ina;
   inout lower_io;
   output lower_out;
   input sec_ina;
   inout sec_io;
   output sec_out;

   wire   lower_out = lower_ina | lower_io;
   wire   sec_out = sec_ina | sec_io;

endmodule

