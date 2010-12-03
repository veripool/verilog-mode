module TOP (/*AUTOARG*/
   // Outputs
   SIG_NAMEB, SIG_NAMEA
   )
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [223:0]	SIG_NAMEA;		// From A of A.v, ...
   output [FOO*2:0]	SIG_NAMEB;		// From C of C.v
   // End of automatics
   /*AUTOINPUT*/
   /*AUTOWIRE*/

   A A(/*AUTOINST*/
       // Outputs
       .SIG_NAMEA			(SIG_NAMEA[224*1-1:128*1]));
   B B(/*AUTOINST*/
       // Outputs
       .SIG_NAMEA			(SIG_NAMEA[127:0]));
   C C(/*AUTOINST*/
       // Outputs
       .SIG_NAMEB			(SIG_NAMEB[FOO*4-2*1:0]));
endmodule

module A(/*AUTOARG*/
   // Outputs
   SIG_NAMEA
   );
   output [224*1-1:128*1] SIG_NAMEA;
   //output [223:128] SIG_NAMEA;
endmodule


module B(/*AUTOARG*/
   // Outputs
   SIG_NAMEA
   );
   output [127:0] SIG_NAMEA;
endmodule


module C(/*AUTOARG*/
   // Outputs
   SIG_NAMEB
   );
   output [FOO*4-2*1:0] SIG_NAMEB;
endmodule


