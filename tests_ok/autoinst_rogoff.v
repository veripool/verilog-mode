module  testmux();
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
   wire [WIDTH-1:0] boo_out_symbolic; // From testmux_boo of testmux.v
   wire [WIDTH-1:0] boo_out_value; // From testmux_boo of testmux.v, ...
   wire [WIDTH-1:0] defaultwidth_out_symbolic;// From testmux_defaultwidth of testmux.v
   // End of automatics
   
   /*AUTO_LISP(setq verilog-auto-inst-param-value nil)*/
   
   /* testmux AUTO_TEMPLATE "testmux_\(.*\)" (
    .a (@_a_symbolic[]),
    .out (@_out_symbolic[]),
    );
    */
   
   testmux #(.WIDTH(  16  )) testmux_boo
     (/*AUTOINST*/
      // Outputs
      .out                              (boo_out_symbolic[WIDTH-1:0]), // Templated
      // Inputs
      .sel                              (sel[2:0]),
      .a                                (boo_a_symbolic[WIDTH-1:0])); // Templated
   
   testmux  testmux_defaultwidth
     (/*AUTOINST*/
      // Outputs
      .out                              (defaultwidth_out_symbolic[WIDTH-1:0]), // Templated
      // Inputs
      .sel                              (sel[2:0]),
      .a                                (defaultwidth_a_symbolic[WIDTH-1:0])); // Templated
   
   //======================================================================
   
   /*AUTO_LISP(setq verilog-auto-inst-param-value t)*/
   
   /* testmux AUTO_TEMPLATE "testmux_\(.*\)" (
    .a (@_a_value[]),
    .out (@_out_value[]),
    );
    */
   
   testmux #(.IGNORE((1)),
             .WIDTH(  16  ),
             .IGNORE2(2))
   testmux_boo
     (/*AUTOINST*/
      // Outputs
      .out                              (boo_out_value[15:0]),   // Templated
      // Inputs
      .sel                              (sel[2:0]),
      .a                                (boo_a_value[15:0]));    // Templated
   
   //======================================================================
   
   testmux #(.IGNORE((1)),
             .WIDTH(WIDTH),   // Make sure we don't recurse!
             .IGNORE2(2))
   testmux_boo
     (/*AUTOINST*/
      // Outputs
      .out                              (boo_out_value[WIDTH-1:0]), // Templated
      // Inputs
      .sel                              (sel[2:0]),
      .a                                (boo_a_value[WIDTH-1:0])); // Templated
   
endmodule
