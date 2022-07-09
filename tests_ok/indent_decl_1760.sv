module test (
             input logic  a,
             output logic b
             );
   
   for (genvar i=0; i<2; i++) begin : g_slice
      
      submod
                 u_sub_0 #(
                           .RESET_POL (RESET_POL)
                           )(
                             .clk     (clk),
                             .reset_n (reset_n),
                             .d       (d[i]),
                             .q       (q_0[i])
                             );
      
      submod
        u_sub_1 #(
                  .RESET_POL (RESET_POL)
                  )(
                    .clk     (clk),
                    .reset_n (reset_n),
                    .d       (q_0[i]),
                    .q       (q[i])
                    );
      
   end
   
endmodule


// Local Variables:
// indent-tabs-mode: nil
// End:
