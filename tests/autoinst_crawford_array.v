`define AUTO_NBR_A_INST 2

module autoinst_crawford_array(/*AUTOARG*/
   // Outputs
   a_valid, a_data,
   // Inputs
   a_ready, clk, rst_n
   );

   // a interface
   output [`AUTO_NBR_A_INST*1-1:0] a_valid;
   output [`AUTO_NBR_A_INST*8-1:0] a_data;
   input [`AUTO_NBR_A_INST*1-1:0]  a_ready;

   // clock interface
   input 			   clk;
   input 			   rst_n;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics

   // non-arrayed example
   autoinst_crawford_array_a auto_a_0
     (/*AUTOINST*/
      // Outputs
      .a_valid				(a_valid),
      .a_data				(a_data[7:0]),
      // Inputs
      .a_ready				(a_ready),
      .clk				(clk),
      .rst_n				(rst_n));

   autoinst_crawford_array_a auto_a_1
     (/*AUTOINST*/
      // Outputs
      .a_valid				(a_valid),
      .a_data				(a_data[7:0]),
      // Inputs
      .a_ready				(a_ready),
      .clk				(clk),
      .rst_n				(rst_n));

   // Arrayed instances
   // AUTOINST does not work for this one :-(
   // Note it is tricky because I want clk and rst_n to fanout to both instances,
   // but I want the valid signals to be discreatly tied to each submodule.

   //autoinst_crawford_array_a ary [`AUTO_NBR_A_INST-1:0]
   //  (/*XXXAUTOINST*/
   //   // Outputs
   //   .a_valid                           (a_valid[1:0]),
   //   .a_data                            (a_data[15:0]),
   //   // Inputs
   //   .a_ready                           (a_ready[1:0]),
   //   .clk                               (clk),
   //   .rst_n                             (rst_n));

   autoinst_crawford_array_a ary [`AUTO_NBR_A_INST-1:0]
     (/*AUTOINST*/
      // Outputs
      .a_valid				(a_valid),
      .a_data				(a_data[7:0]),
      // Inputs
      .a_ready				(a_ready),
      .clk				(clk),
      .rst_n				(rst_n));

   autoinst_crawford_array_a #(.a(a),b) par [`AUTO_NBR_A_INST-1:0]
     (/*AUTOINST*/
      // Outputs
      .a_valid				(a_valid),
      .a_data				(a_data[7:0]),
      // Inputs
      .a_ready				(a_ready),
      .clk				(clk),
      .rst_n				(rst_n));

endmodule
