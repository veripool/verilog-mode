// Note module names don't match, this is intentional to check the .f file

module reg_core (
                 output logic [7:0] q,
                 input logic [7:0]  d,
                 input logic        clk, rst_n
                 /*AUTOARG*/);
   
   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n) q <= '0;
   else        q <= d;
endmodule

module register (
                 output logic [7:0] q,
                 input logic [7:0]  d,
                 input logic        clk, rst_n
                 /*AUTOARG*/);
   
   reg_core c1 (
                /*AUTOINST*/
                // Outputs
                .q                      (q[7:0]),
                // Inputs
                .d                      (d[7:0]),
                .clk                    (clk),
                .rst_n                  (rst_n));
endmodule
