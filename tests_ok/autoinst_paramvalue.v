module  testmuxpv();
   # (parameter WIDTH = 32)
   (
    input wire [2:0]       /* synopsys enum cur_info */ sel,
    input wire [WIDTH-1:0] a,
    output reg [WIDTH-1:0] out
    );
endmodule

module  top_test();
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [WIDTH-1:0] out;                        // From testmuxpv_boo of testmuxpv.v, ..., Couldn't Merge
   // End of automatics
   
   //======================================================================
   
   /* testmuxpv AUTO_TEMPLATE (
    ) */
   
   testmuxpv #(.IGNORE((1)),
               .WIDTH(  16  ),
               .IGNORE2(2))
   testmuxpv_boo
     (/*AUTOINST*/
      // Outputs
      .out                              (out[15:0]),
      // Inputs
      .sel                              (sel[2:0]),
      .a                                (a[15:0]));
   
   //======================================================================
   
   testmuxpv #(.IGNORE((1)),
               .WIDTH(WIDTH),   // Make sure we don't recurse!
               .IGNORE2(2))
   testmuxpv_boo
     (/*AUTOINST*/
      // Outputs
      .out                              (out[WIDTH-1:0]),
      // Inputs
      .sel                              (sel[2:0]),
      .a                                (a[WIDTH-1:0]));
   
   //======================================================================
   // bug331: vl-width should correct when param values propagating
   
   /* testmuxpv AUTO_TEMPLATE (
    .a ({@"vl-width"{1'b0}}),
    ) */
   
   testmuxpv #(.IGNORE((1)),
               .WIDTH(16),
               .IGNORE2(2))
   testmuxpv_boo
     (/*AUTOINST*/
      // Outputs
      .out                              (out[15:0]),
      // Inputs
      .sel                              (sel[2:0]),
      .a                                ({16{1'b0}}));           // Templated
   
endmodule

// Local Variables:
// verilog-auto-inst-param-value:t
// End:
