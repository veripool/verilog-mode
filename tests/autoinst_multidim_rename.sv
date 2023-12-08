module parent(/*AUTOARG*/);
  input  [31:0][7:0] data_in;
  output [4:0]       meta_out;
  output [4:0]       meta_out_no_rename;
  output [31:0][7:0] data_out;

  /*AUTOWIRE*/

  /* child1 AUTO_TEMPLATE (
    .data_out                 (child1_out[][]),
    .meta_out                 (child1_meta_out[]),
  ); */
  child1 U1 (
    /*AUTOINST*/
  )

  /* child2 AUTO_TEMPLATE (
    .data_in                 (child1_out[][]),
    .meta_in                 (child1_meta_out[]),
  ); */
  child2 U2 (
    /*AUTOINST*/
  )

endmodule

module child1(/*AUTOARG*/);
  input  [31:0][7:0] data_in;
  output [31:0][7:0] data_out;
  output [4:0]       meta_out;

endmodule

module child2(/*AUTOARG*/);
  input  [31:0][7:0] data_in;
  input  [4:0]       meta_in;
  output [31:0][7:0] data_out;
  output [4:0]       meta_out_no_rename;

endmodule

// Local Variables:
// verilog-auto-inst-vector:nil
// End:
