module inject_inst_param;
   parameter         WIDTH = 8;
   logic [WIDTH-1:0] q;
   logic [WIDTH-1:0] d;
   logic             clk, rst_n;
   
   register #(.WIDTH(WIDTH)) r1 (
                                 /*AUTOINST*/
                                 // Outputs
                                 .q             (q[WIDTH-1:0]),
                                 // Inputs
                                 .d             (d[WIDTH-1:0]),
                                 .clk           (clk),
                                 .rst_n         (rst_n));
endmodule

module register #(parameter WIDTH=4) (
                                      output logic [WIDTH-1:0] q,
                                      input logic [WIDTH-1:0]  d,
                                      input logic              clk, rst_n
                                      /*AUTOARG*/);
   
   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n) q <= '0;
   else        q <= d;
endmodule
