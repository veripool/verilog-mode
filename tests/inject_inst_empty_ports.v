module inject_inst_empty_ports;
  logic [7:0] q;
  logic [7:0] d;
  logic       clk, rst_n;

  register r1 (.q(q),
               .qb(), // unconnect output
               .d(d),
               .clk(clk),
               .rst_n(rst_n)
               );
endmodule

module register (
  output logic [7:0] q, qb,
  input  logic [7:0] d,
  input  logic       clk, rst_n
  );

  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= '0;
    else        q <= d;

  assign qb = ~q;
endmodule
