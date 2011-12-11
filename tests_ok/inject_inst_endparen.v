module inject_inst_endparen;
   logic [7:0] q;
   logic [7:0] d;
   logic       clk, nreset;
   
   register r1 (.rst_n(nreset),
                /*AUTOINST*/
                // Outputs
                .q                      (q[7:0]),
                // Inputs
                .d                      (d[7:0]),
                .clk                    (clk));
   
`if NEVER
   register r1 (.q(qKEEP),
                .d(dKEEP),
                .clk(clkKEEP),
                // This is the
                // asynchronous reset
                .rst_n(nreset)
                /*AUTOINST*/);
`endif
   
endmodule

module register (
                 output logic [7:0] q,
                 input logic [7:0]  d,
                 input logic        clk, rst_n
                 /*AUTOARG*/);
   
   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n) q <= '0;
   else        q <= d;
endmodule
