module sub(output logic [1:-1] oned,
           output logic [1:-1] [2:-1] 	     twod,
           output logic [1:-1] [2:-1] [3:-3] threed);
endmodule

module dut (
            );

   /*AUTOWIRE*/

   /* sub AUTO_TEMPLATE ();
   */

   sub sub1 (/*AUTOINST*/);

   /* sub AUTO_TEMPLATE (
	     .oned			(b_oned[]),
	     .twod			(b_twod[]),
	     .threed			(b_threed[]));
   */

   // NOTE this results in the wrong declaration for b_twod/b_threed
   sub subb (/*AUTOINST*/);

   /* sub AUTO_TEMPLATE (
	     .oned			(c_oned[]),
	     .twod			(c_twod[x][]),
	     .threed			(c_threed[x][y][]));
   */

   sub subc (/*AUTOINST*/);

   /* sub AUTO_TEMPLATE (
	     .oned			(d_oned[][]),
	     .twod			(d_twod[][]),
	     .threed			(d_threed[][]));
   */

   sub subd (/*AUTOINST*/);

endmodule
