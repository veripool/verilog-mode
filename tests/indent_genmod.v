// bug1163

module indent;

   generate for (genvar i=0; i<4; i++) begin : gen_inst0
      // Here, AUTOINST line indents incorrectly indents way too far the the right
      // ( below indents after = above, which is incorrect
      subindent s
			  (/*AUTOINST*/
			   // Outputs
			   .y			(y),
			   // Inputs
			   .a			(a));
   end endgenerate

   // Without the '=0', the AUTOINST line indents properly
   generate for (genvar i; i<4; i++) begin : gen_inst1
      subindent s
        (/*AUTOINST*/
	 // Outputs
	 .y				(y),
	 // Inputs
	 .a				(a));
   end endgenerate

endmodule

module subindent (input a, output y);
endmodule
