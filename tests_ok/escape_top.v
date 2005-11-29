module escape_top (/*AUTOARG*/
   // Outputs
   \o[2] , \o[10] ,
   // Inputs
   \i&e;
   );

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		\i&e; ;			// To a of escape_a.v
   // End of automatics
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		\o[10] ;		// From a of escape_a.v
   output		\o[2] ;			// From a of escape_a.v
   // End of automatics

   escape_a a (/*AUTOINST*/
	       // Outputs
	       .\o[10] 			(\o[10] ),
	       .\o[2] 			(\o[2] ),
	       // Inputs
	       .\i&e; 			(\i&e; ));

endmodule
