module autosense (/*AUTOARG*/);

   input ina;
   input inb;
   input inc;
   output [1:0] out;
   output 	out2;

   /*AUTOREG*/

`include "autosense_inc_param.v"
`include "autosense_one.v"
`define Input ina

   always @(/*AUTOSENSE*/) begin
      case (inc)
	1'b1: out = {`Input ? `one : 1'b0, `Input};
	default: out = {2{inb}};
      endcase
   end


   always @(/*AUTOSENSE*/) begin
      out2 = `Input | PARAM_TWO | PARAM_THREE | PARAM_FOUR;
   end

   always @(*) begin
      // @ (/*AS*/)
      out3 = ina;
   end

   always @* begin
      out3 = ina;
   end

endmodule
// Local Variables:
// verilog-auto-read-includes:t
// End:
