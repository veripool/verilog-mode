module foo (
input wire a,
input wire b,
output reg z
);

parameter VAR = 0;

generate
if (VAR)
inst inst(
.a(a),
.b(b),
.z(z)
);
else
inst2 inst2 (
.a(a),
.b(b),
.z(z)
);
endgenerate

endmodule


// Local Variables:
// verilog-indent-lists: nil
// End:
