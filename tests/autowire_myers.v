module test1 ( wireA, wireB );
    output [3:0] wireA;
    output [16:0] wireB;
endmodule

module test_top;

   /*AUTOWIRE*/

   generate
      if (1) begin
	 test1 t1 (/*AUTOINST*/);
      end
      else begin
	 assign wireA = 0;
      end
   endgenerate
endmodule
