module foo (
input wire a,
input wire b,
output reg z
);

localparam CONST=1;

generate
for (genvar i=0; i<CONST; i++)
inst inst(
.a(a[i]),
.b(b[i]),
.z(z[i])
);
endgenerate

endmodule


// Local Variables:
// verilog-indent-lists: nil
// End:
