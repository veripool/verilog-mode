module parent(/*AUTOARG*/
              // Outputs
              meta_out, meta_out_no_rename, data_out,
              // Inputs
              data_in
              );
   input [31:0][7:0]  data_in;
   output [4:0]       meta_out;
   output [4:0]       meta_out_no_rename;
   output [31:0][7:0] data_out;
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [4:0]         child1_meta_out; // From U1 of child1.v
   wire [31:0] [7:0]  child1_out;      // From U1 of child1.v
   // End of automatics
   
   /* child1 AUTO_TEMPLATE (
    .data_out                 (child1_out[][]),
    .meta_out                 (child1_meta_out[]),
    ); */
   child1 U1 (
              /*AUTOINST*/
              // Outputs
              .data_out                 (child1_out/*[31:0][7:0]*/), // Templated
              .meta_out                 (child1_meta_out[4:0]),  // Templated
              // Inputs
              .data_in                  (data_in/*[31:0][7:0]*/));
   
   /* child2 AUTO_TEMPLATE (
    .data_in                 (child1_out[][]),
    .meta_in                 (child1_meta_out[]),
    ) */
   child2 U2 (
              /*AUTOINST*/
              // Outputs
              .data_out                 (data_out/*[31:0][7:0]*/),
              .meta_out_no_rename       (meta_out_no_rename),
              // Inputs
              .data_in                  (child1_out/*[31:0][7:0]*/), // Templated
              .meta_in                  (child1_meta_out[4:0]));         // Templated
   
endmodule

module child1(/*AUTOARG*/
              // Outputs
              data_out, meta_out,
              // Inputs
              data_in
              )
  input [31:0][7:0]  data_in;
   output [31:0][7:0] data_out;
   output [4:0]       meta_out;
   
endmodule

module child2(/*AUTOARG*/
              // Outputs
              data_out, meta_out_no_rename,
              // Inputs
              data_in, meta_in
              );
   input [31:0][7:0]  data_in;
   input [4:0]        meta_in;
   output [31:0][7:0] data_out;
   output [4:0]       meta_out_no_rename;
   
endmodule

// Local Variables:
// verilog-auto-inst-vector:nil
// End:
