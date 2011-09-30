typedef struct packed {
   logic [7:0] data;
   logic       wr_ena;
} mystruct_s;

module submod
  (input logic a_port,
   input logic [4:0] b_bus,
   input             mystruct_s single_struct_is_fine,
   input             mystruct_s [2:0] array_of_struct_is_not,
   output logic      status);
   
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   wire status = 1'h0;
   // End of automatics
   
endmodule // submod

module top;
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic status; // From submod0 of submod.v
   // End of automatics
   
   /*AUTOREGINPUT*/
   // Beginning of automatic reg inputs (for undeclared instantiated-module inputs)
   logic a_port;                        // To submod0 of submod.v
   mystruct_s [2:0]     array_of_struct_is_not; // To submod0 of submod.v
   logic [4:0] b_bus;                   // To submod0 of submod.v
   mystruct_s           single_struct_is_fine;  // To submod0 of submod.v
   // End of automatics
   
   submod submod0
     (/*AUTOINST*/
      // Outputs
      .status                           (status),
      // Inputs
      .a_port                           (a_port),
      .b_bus                            (b_bus[4:0]),
      .single_struct_is_fine            (single_struct_is_fine),
      .array_of_struct_is_not           (array_of_struct_is_not[2:0]));
endmodule // top

// Local Variables:
// verilog-typedef-regexp: "_s$"
// End:
