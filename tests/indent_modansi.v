module testmodule(
		   input wire [1:0]   pin1,
		   input wire 	      pin2,
		   input wire [1:0]   pin3,
		   input wire 	      pin4,
		   output wire 	      pin5,
		   output wire [10:0] pin6,
		   output reg 	      pin7,
		   output reg [1:0]   pin8
		   );
   initial begin
      $display("alls well that ends well");
   end
endmodule // testmodule


