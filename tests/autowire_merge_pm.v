// issue #1879

module TOP
  (
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [DW-1:0]	SIG_NAMEA		// From A of A.v
   // End of automatics
   /*AUTOINPUT*/
   );
   /*AUTOWIRE*/

   A A(/*AUTOINST*/
       // Outputs
       .SIG_NAMEA			(SIG_NAMEA[DW-1+2:0]));

endmodule

module A
  (
   output [DW-1+2:0] SIG_NAMEA
   );
endmodule
