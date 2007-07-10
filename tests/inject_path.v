module inject_path;
  logic [7:0] q;
  logic [7:0] d;
  logic       clk, rst_n;

  register r1 (.q(q), .d(d), .clk(clk), .rst_n(rst_n));
endmodule

// Local Variables:
// mode: Verilog
// verilog-library-flags:("-f inject_path.f")
// End:
