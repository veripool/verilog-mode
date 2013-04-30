// bug637

module submod_a
  (
   //Inputs
   input wire signed [15:0]  serial_in,
   //Outputs
   output wire signed [15:0] parallel_out [0:7]
   );
endmodule

module submod_b
  (
   //Inputs
   input wire signed [15:0]  parallel_out [0:7],
   //Outputs
   output wire signed [15:0] final_out [0:7]
   );
endmodule

module top
  (
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input logic signed [15:0]  serial_in, // To a_inst of submod_a.v
   // End of automatics
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output logic signed [15:0] final_out [0:7]   // From b_inst of submod_b.v
   // End of automatics
   );
   
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic signed [15:0] parallel_out [0:7];      // From a_inst of submod_a.v
   // End of automatics
   
   submod_a a_inst
     (/*AUTOINST*/
      // Outputs
      .parallel_out                     (parallel_out/*[15:0]*/),
      // Inputs
      .serial_in                        (serial_in[15:0]));
   
   submod_b b_inst
     (/*AUTOINST*/
      // Outputs
      .final_out                        (final_out/*[15:0]*/),
      // Inputs
      .parallel_out                     (parallel_out/*[15:0]*/));
   
   
endmodule
