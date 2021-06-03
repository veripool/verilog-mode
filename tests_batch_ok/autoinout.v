module io1_sub(
	       /*AUTOARG*/
	       // Outputs
	       sec_out, lower_out,
	       // Inouts
	       sec_io, lower_io,
	       // Inputs
	       sec_ina, lower_ina
	       );

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		lower_ina;		// To instio of instio.v
   input		sec_ina;		// To instio of instio.v
   // End of automatics

   /*AUTOINOUT*/
   // Beginning of automatic inouts (from unused autoinst inouts)
   inout		lower_io;		// To/From instio of instio.v
   inout		sec_io;			// To/From instio of instio.v
   // End of automatics

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		lower_out;		// From instio of instio.v
   output		sec_out;		// From instio of instio.v
   // End of automatics

   /* inst AUTO_TEMPLATE (
    .lower_inb		(1'b1),
    )*/


   instio instio (/*AUTOINST*/
		  // Outputs
		  .lower_out		(lower_out),
		  .sec_out		(sec_out),
		  // Inouts
		  .lower_io		(lower_io),
		  .sec_io		(sec_io),
		  // Inputs
		  .lower_ina		(lower_ina),
		  .sec_ina		(sec_ina));

endmodule

module instio (/*AUTOARG*/
	       // Outputs
	       lower_out, sec_out,
	       // Inouts
	       lower_io, sec_io,
	       // Inputs
	       lower_ina, sec_ina
	       );

   input lower_ina;
   inout lower_io;
   output lower_out;
   input  sec_ina;
   inout  sec_io;
   output sec_out;

   wire	  lower_out = lower_ina | lower_io;
   wire	  sec_out = sec_ina | sec_io;

endmodule

