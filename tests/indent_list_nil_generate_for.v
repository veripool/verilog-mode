module foo (
input wire a,
input wire b,
output reg z
);

localparam CONST=1;

generate
for (genvar i=0; i<CONST; i++) begin : label
inst inst(
.a(a[i]),
.b(b[i]),
.z(z[i])
);
end : label
endgenerate

endmodule


// Local Variables:
// verilog-indent-lists: nil
// End:
