module sub1 (/*AUTOARG*/
   // Inouts
   busout,
   // Inputs
   bus1
   );

   input [3:0] bus1;
   inout [3:0] busout;

   wire 	busout = bus1;

endmodule


module autoinput_concat_lau
  (
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   // End of automatics
   /*AUTOINOUT*/
   // Beginning of automatic inouts (from unused autoinst inouts)
   // End of automatics
   );

   /* sub1 AUTO_TEMPLATE (
	      .busout	({2'b0,fooout[1:0]}),
	      .bus1	({2'b0,~foo[1:0]}),
    );
    */

   sub1 sub1 (/*AUTOINST*/
	      // Inouts
	      .busout			({2'b0,fooout[1:0]}),	 // Templated
	      // Inputs
	      .bus1			({2'b0,~foo[1:0]}));	 // Templated

endmodule

