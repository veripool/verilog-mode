module align_assign_expr (
input logic clk,
input logic rst_n,
input logic [3:0] i,
output logic o1,
output logic [3:0] o2,
output logic [3:0] o3
);

parameter WIDTH = 4;

logic [WIDTH-1:0] temp1 = 4'h0;
logic temp2 = 1'b0;
logic signed temp3 = '0;

always_ff @(posedge clk) begin : label
if (!rst_n) begin
o1 <= 1'b0;
o2[1:0] <= 2'b00;
o2[3] <= 1'b1;
o2[4] <= 1'b0;
o3 <= 4'h0;
end
else begin
o1 <= 1'b1;
o2[1:0] <= 2'b11;
o2[3] <= 1'b0;
o2[4] <= 1'b1;
o3 <= 4'h1;
end
end : label

assign o1 = &i;
assign o2[1:0] = i[1:0];
assign o2[WIDTH-1:2] = i[3:0];
assign o3[0] = i;
assign o3[1] = i;
assign o3[3:2] = {i, i};

endmodule : align_assign_expr

// Local Variables:
// verilog-align-assign-expr: t
// End:
