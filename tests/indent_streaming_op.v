module test (input logic clk,
             input logic a,
             output logic c,
             output byte  d[4]);

always_ff @(posedge clk) begin
if (a == 1'b1) begin
data <= {<<byte{$urandom()}};
c <= data[1] > 8'h0f;
end
end
endmodule // test
