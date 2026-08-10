// issue #1879

module TOP
  (
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [DW+1:0] SIG_NAMEA, // From A of A.v
   output [DW-1:0] SIG_NAMEB, // From A of A.v
   output [DW-2:0] SIG_NAMEC, // From A of A.v
   output [DW-0:0] SIG_NAMED  // From A of A.v
   // End of automatics
   /*AUTOINPUT*/
   );
   /*AUTOWIRE*/
   
   A A(/*AUTOINST*/
       // Outputs
       .SIG_NAMEA                       (SIG_NAMEA[DW-1+2:0]),
       .SIG_NAMEB                       (SIG_NAMEB[DW+1-2:0]),
       .SIG_NAMEC                       (SIG_NAMEC[DW-3+1:0]),
       .SIG_NAMED                       (SIG_NAMED[DW-1+1:0]));
   
endmodule

module A
  (
   output [DW-1+2:0] SIG_NAMEA,
   output [DW+1-2:0] SIG_NAMEB,
   output [DW-3+1:0] SIG_NAMEC,
   output [DW-1+1:0] SIG_NAMED
   );
endmodule
