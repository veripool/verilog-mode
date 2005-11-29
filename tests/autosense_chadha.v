module test (/*AUTOARG*/
   // Outputs
   out1, out2,
   // Inputs
   sel, in0, in1, in2
   );

   input [1:0]     sel;
   input  	   in0, in1, in2;

   output 	   out1;
   output 	   out2;

   reg 		   out1;
   reg 		   out2;

   // Missing in2
   always @ (/*AS*/in0 or in1 or in2 or sel)
     if (sel == 2'b00)
       begin
	  out1 = in1;
	  out2 = in0;
       end
     else
       begin
	  out1 = in2;
	  out2 = in1;
       end

   // OK
   always @ (/*AS*/in1 or in2 or sel)
     if (sel == 2'b00)
       out1 = in1;
     else
       out1 = in2;

endmodule // test
