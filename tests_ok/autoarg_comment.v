module autoarg_comment
  
  // Copyright 1997-1998, blah, blah, blah
  
  (/*AUTOARG*/
   // Outputs
   outgo2,
   // Inputs
   income
   );
   
   //verilint 332 OFF   //* Not all possible cases covered, but default case exists
  
   input  (* ATTRIB="val" *) income;
   output outgo2;
   
endmodule
