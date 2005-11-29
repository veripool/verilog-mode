module bfm (/*AUTOARG*/
   // Inputs
   name
   );
   input [8*5:1] name ;
endmodule

module tb;
   // -------------------------------------------------------------------------
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   // End of automatics
   // -------------------------------------------------------------------------
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   // End of automatics
   // -------------------------------------------------------------------------
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics
   // -------------------------------------------------------------------------
   /* AUTO_CONSTANT ( "name0" "name1" "name2" ) */
   // -------------------------------------------------------------------------
   /* bfm AUTO_TEMPLATE (
    // Inputs
    .name ("name@"));
    */
   // -------------------------------------------------------------------------
   bfm bmf0 (/*AUTOINST*/
	     // Inputs
	     .name			("name0"));		 // Templated
   // -------------------------------------------------------------------------
   bfm bmf1 (/*AUTOINST*/
	     // Inputs
	     .name			("name1"));		 // Templated
   // -------------------------------------------------------------------------
   bfm bmf2 (/*AUTOINST*/
	     // Inputs
	     .name			("name2"));		 // Templated
   // -------------------------------------------------------------------------
endmodule
