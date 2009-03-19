module sub1 (/*AUTOARG*/);

   input [3:0] bus1;
   inout [3:0] busout;

   wire 	busout = bus1;

endmodule


module autoinput_concat_lau
  (
   /*AUTOINPUT*/
   /*AUTOINOUT*/
   );

   /* sub1 AUTO_TEMPLATE (
	      .busout	({2'b0,fooout[1:0]}),
	      .bus1	({2'b0,~foo[1:0]}),
    );
    */

   sub1 sub1 (/*AUTOINST*/);

endmodule

