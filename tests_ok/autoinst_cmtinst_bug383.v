module t;
   
   /*fifo_s AUTO_TEMPLATE (
    .ignored_signal         (1'b1),
    .out_signal             (NC),
    .out_bus                (out_bus[]),
    );
    */
   fifo_s data_fifo (
                     //fifo_s data_fifo (
                     // Inputs
                     .clk                  (fifo_clk),
                     /*AUTOINST*/
                     // Outputs
                     .out_bus           (out_bus[31:0]),         // Templated
                     .out_signal        (NC),                    // Templated
                     // Inputs
                     .ignored_signal    (1'b1),                  // Templated
                     .reset             (reset));
   
   /*fifo_s AUTO_TEMPLATE (
    .ignored_signal         (1'b1),
    .out_signal             (NC),
    .out_bus                (out_bus[]),
    );
    */
   //fifo_s data_fifo (
   fifo_s data_fifo (
                     // Inputs
                     .clk                  (fifo_clk),
                     /*AUTOINST*/
                     // Outputs
                     .out_bus           (out_bus[31:0]),         // Templated
                     .out_signal        (NC),                    // Templated
                     // Inputs
                     .ignored_signal    (1'b1),                  // Templated
                     .reset             (reset));
endmodule

module fifo_s;
   input         ignored_signal;
   input         reset;
   output [31:0] out_bus;
   output        out_signal;
endmodule
