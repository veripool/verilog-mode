module parent
  (
  
   /*AUTOINPUT*/

   /*AUTOOUTPUT*/

   /*AUTOINOUT*/
   );

  
  /*AUTOWIRE*/

  
  child_a sub_module
    (/*AUTOINST*/);

  child_b sub_module
    (/*AUTOINST*/);  
  
endmodule // parent

module child_a
  (
   input [3:0]   a,
   input [3:0]   a2,
   input [3:0]   a3,
   input [3:0]   a4,   
   inout [5:0]   c,
   inout [5:0]   c2,
   inout         c3,
   output [2:0]  b,
   output [2:0]  b2,
   output [2:0]  b3,
   output [2:0]  b4,
   input         clk,
   output        d
   );
endmodule

  
module child_b
  (
   output [3:0]   a,
   output [3:0]   a4,   
   inout [5:0]    c,
   inout [5:0]    c2,
   inout          c3,
   input [2:0]    b,
   input [2:0]    b2,
   input [2:0]    b3,
   input [2:0]    b4,
   input          clk
   );  
endmodule
