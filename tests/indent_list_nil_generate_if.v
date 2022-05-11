module foo (
input wire a,
input wire b,
output reg z
);

parameter VAR = 0;

generate
if (VAR) begin
inst inst(
.a(a),
.b(b),
.z(z)
);
end
else begin
inst2 inst2 (
.a(a),
.b(b),
.z(z)
);
end
endgenerate

endmodule


// Local Variables:
// verilog-indent-lists: nil
// End:
