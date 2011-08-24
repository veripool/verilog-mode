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
                     /*AUTOINST*/);

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
                     /*AUTOINST*/);
endmodule

module fifo_s;
   input ignored_signal;
   input reset;
   output [31:0] out_bus;
   output 	 out_signal;
endmodule
