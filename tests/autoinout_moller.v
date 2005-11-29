module a ( /*AUTOARG*/
   // Outputs
   o1,
   // Inouts
   io1,
   // Inputs
   i1
   ) ;

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		i1;			// To b of b.v
   // End of automatics

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		o1;			// From b of b.v
   // End of automatics

   /*AUTOINOUT*/
   // Beginning of automatic inouts (from unused autoinst inouts)
   inout		io1;			// To/From b of b.v
   // End of automatics

   b b
     (/*AUTOINST*/
      // Outputs
      .o1				(o1),
      // Inouts
      .io1				(io1),
      // Inputs
      .i1				(i1));

endmodule // a

module b (/*AUTOARG*/
   // Outputs
   o1,
   // Inouts
   io1,
   // Inputs
   i1
   ) ;

   input i1 ;
   output o1 ;
   inout  io1 ;

endmodule // b
