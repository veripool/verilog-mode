module inject_inst_net_case (
                             output logic [7:0] q2,
                             input logic [7:0]  d,
                             input logic        clk, rst_n
                             /*AUTOARG*/);
   logic [7:0] Q1;
   
   register2 r2 (.q1(Q1), .ck(clk),
                 /*AUTOINST*/
                 // Outputs
                 .q2                    (q2[7:0]),
                 // Inputs
                 .rst_n                 (rst_n));
   
   register1 r1 (.q1(Q1), .ck(clk),
                 /*AUTOINST*/
                 // Inputs
                 .d                     (d[7:0]),
                 .rst_n                 (rst_n));
endmodule

module register2 (
                  output logic [7:0] q2,
                  input logic [7:0]  q1,
                  input logic        ck, rst_n
                  /*AUTOARG*/);
   
   always_ff @(posedge ck or negedge rst_n)
     if (!rst_n) q2 <= '0;
   else        q2 <= q1;
endmodule

module register1 (
                  output logic [7:0] q1,
                  input logic [7:0]  d,
                  input logic        ck, rst_n
                  /*AUTOARG*/);
   
   always_ff @(posedge ck or negedge rst_n)
     if (!rst_n) q1 <= '0;
   else        q1 <= d;
endmodule
