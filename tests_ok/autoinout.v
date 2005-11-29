module io1_sub(
	       /*AUTOARG*/
   // Outputs
   lower_out,
   // Inouts
   lower_io,
   // Inputs
   lower_ina
   );

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		lower_ina;		// To instio of instio.v
   // End of automatics

   /*AUTOINOUT*/
   // Beginning of automatic inouts (from unused autoinst inouts)
   inout		lower_io;		// To/From instio of instio.v
   // End of automatics

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		lower_out;		// From instio of instio.v
   // End of automatics

   /* inst AUTO_TEMPLATE (
    .lower_inb		(1'b1),
    )*/


   instio instio (/*AUTOINST*/
		  // Outputs
		  .lower_out		(lower_out),
		  // Inouts
		  .lower_io		(lower_io),
		  // Inputs
		  .lower_ina		(lower_ina));

endmodule

module instio (/*AUTOARG*/
   // Outputs
   lower_out,
   // Inouts
   lower_io,
   // Inputs
   lower_ina
   );

   input lower_ina;
   inout lower_io;
   output lower_out;

   wire   lower_out = lower_ina | lower_io;

endmodule

