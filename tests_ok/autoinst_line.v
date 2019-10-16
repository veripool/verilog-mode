module foo();
   bar i0 (
           /*AUTOINST*/
           // Outputs
           .c                           (c),
           // Inputs
           .a                           (a),
           .b                           (b),
           .clk                         (clk));
endmodule // foo

module bar(
`line 2 "bar.v" 0
           input logic  a,
`line 3 "bar.v" 0
           input logic  b,
`line 4 "bar.v" 0
           output logic c,
`line 5 "bar.v" 0
           input logic  clk
`line 6 "bar.v" 0
           );
endmodule // bar
