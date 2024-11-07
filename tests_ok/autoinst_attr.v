// Issue #1884

module top
  (
   
   (* period= 5.0 *)
   input logic clk,
   
   (* asynchronous=true *)
   input logic rst_n,
   
   (* attribute1="hello" *)
   /*AUTOINPUT("^a_")*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input logic [7:0]    a_data,                 // To i_module_a of module_a.v
   input logic          a_valid,                // To i_module_a of module_a.v
   // End of automatics
   /*AUTOOUTPUT("^a_")*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output logic         a_ready,                // From i_module_a of module_a.v
   // End of automatics
   
   /*AUTOINPUT("^z_")*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input logic          z_ready,                // To i_module_b of module_b.v
   // End of automatics
   /*AUTOOUTPUT("^z_")*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output logic [7:0]   z_data,                 // From i_module_b of module_b.v
   output logic         z_valid         // From i_module_b of module_b.v
   // End of automatics
   
   /*AUTOOUTPUT*/
   );
   
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [7:0] b_data;  // From i_module_a of module_a.v
   logic       b_ready; // From i_module_b of module_b.v
   logic       b_valid; // From i_module_a of module_a.v
   // End of automatics
   
   module_a i_module_a
     (/*AUTOINST*/
      // Outputs
      .a_ready                          (a_ready),
      .b_data                           (b_data[7:0]),
      .b_valid                          (b_valid),
      // Inputs
      .clk                              (clk),
      .rst_n                            (rst_n),
      .a_data                           (a_data[7:0]),
      .a_valid                          (a_valid),
      .b_ready                          (b_ready));
   
   module_b i_module_b
     (/*AUTOINST*/
      // Outputs
      .b_ready                          (b_ready),
      .z_data                           (z_data[7:0]),
      .z_valid                          (z_valid),
      // Inputs
      .clk                              (clk),
      .rst_n                            (rst_n),
      .b_data                           (b_data[7:0]),
      .b_valid                          (b_valid),
      .z_ready                          (z_ready));
   
endmodule

module module_a
  (
   input logic        clk,
   input logic        rst_n,
   
   input logic [7:0]  a_data,
   input logic        a_valid,
   output logic       a_ready,
   
   output logic [7:0] b_data,
   output logic       b_valid,
   input logic        b_ready
   );
endmodule

module module_b
  (
   input logic        clk,
   input logic        rst_n,
   
   input logic [7:0]  b_data,
   input logic        b_valid,
   output logic       b_ready,
   
   output logic [7:0] z_data,
   output logic       z_valid,
   input logic        z_ready
   );
endmodule
