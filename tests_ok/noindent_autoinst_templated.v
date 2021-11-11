// Tests that final ); has right indent

module autoinst_autonohookup (
                              /*AUTOINPUT*/
			      // Beginning of automatic inputs (from unused autoinst inputs)
			      input	      i1,		      // To a2 of a2.v
			      // End of automatics
                              /*AUTOOUTPUT*/
			      // Beginning of automatic outputs (from unused autoinst outputs)
			      output	      o1		      // From a2 of a2.v
			      // End of automatics
                              );
   /* a2 AUTO_TEMPLATE (
    .i1(i1),
    .o1(o1),
    ) */
   a2 a2(/*AUTOINST*/
	 // Outputs
	 .o1				(o1),			 // Templated
	 // Inputs
	 .i1				(i1));			 // Templated
endmodule

module a2 (
           input  i1,
           output o1
           );
endmodule

