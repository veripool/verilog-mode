module batch_li_parent (/*AUTOARG*/
			// Inputs
			clk, rst
			);

   input rst;
   input clk;

   parameter WIDTH_0 = 8;
   parameter WIDTH_1 = 16;
   
   batch_li_child
     #(.WIDTH_1 (WIDTH_0),
       .WIDTH_0 (WIDTH_1))
   child
     (/*AUTOINST*/
      // Inputs
      .rst				(rst),
      .clk				(clk));

endmodule

// Local Variables:
// verilog-auto-arg-sort: t
// End:
