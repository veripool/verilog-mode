module comments_test;
   logic [7:0] q1;
   logic [7:0] d;
   logic       clk, rst_n;
   
   register r1 (.q(q1),
                .clk100(clk),
                // Asynchronous reset
                /*AUTOINST*/
                // Inputs
                .d                      (d[7:0]),
                .clk                    (clk),
                .rst_n                  (rst_n));
endmodule

// Local Variables:
// mode: Verilog
// verilog-library-flags:("-f inject_path.f")
// End:
