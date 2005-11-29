module escape_a (/*AUTOARG*/
   // Outputs
   \o[10] , \o[2] ,
   // Inputs
   \i&e; 
   );
   output \o[10] ;
   output \o[2] ;
   input  \i&e; ;

   wire   \o[10] = \i&e; ;
   wire   \o[2] = \i&e; ;

endmodule
