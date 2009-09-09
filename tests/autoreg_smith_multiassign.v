module test(/*AUTOARG*/
   // Outputs
   a1, b1, c1, one
   );

   output [5:0] a1;
   output [5:0] b1;
   output [5:0] c1;

   /*AUTOREG*/

   //wire [5:0]   a2,b2,c2;

   assign {a1,b1,c1} = {a2,b2,c2};

   output [1:0] one;
   assign one = a2[0];

endmodule
