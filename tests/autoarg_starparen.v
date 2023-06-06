// bug #1829
module dut (/*autoarg*/);
input clk;
input rst_n;
output logic d;

always @(* )
begin
  d = 1'b0;
end

endmodule
