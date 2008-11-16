module foo_bar (/*AUTOARG*/
   // Outputs
   result,
   // Inputs
   clk, rst, data, addr
   )

  input        clk;
   input       rst;
   input       signed [15:-15] data;
   input [11:0] 	       addr;
   output 	signed [15:0]  result;

   wire 	signed [15:-15] data;
   reg 		signed [15:0] 	result;

   always @ (/*AS*/rst) begin
      result = 32'sh22 | rst;
   end

endmodule // foo_bar
