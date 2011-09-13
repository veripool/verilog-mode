module t();

   logic [31:0] sum;
   logic [31:0] a;
   logic [31:0] b;
   reg [32:0] tmp;

   always @(posedge clk or negedge rst) begin
      if (!rst) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 sum <= 32'h0;
	 // End of automatics
      end
      else begin
	 //reg [32:0] tmp;
	 tmp = a + b;
	 if (tmp[32])
	   sum <= 32'hffffffff;
	 else
	   sum <= tmp[31:0];
      end
   end

endmodule

// Local Variables:
// verilog-auto-reset-blocking-in-non: nil
// End:
