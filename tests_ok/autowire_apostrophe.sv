module test_port0
  (/*AUTOARG*/
   // Outputs
   d
   );
   output [31:0] d[2];
endmodule // test_port

module test_port1
  (/*AUTOARG*/
   // Inputs
   dd
   );
   input [31:0] dd[2];
endmodule // test_port1

module top()
  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire [31:0] d_1; // From u0 of test_port0.v
   wire [31:0] d_2; // From u0 of test_port0.v
   // End of automatics
   
   /*
    test_port0  AUTO_TEMPLATE
    (
    .d\(.*\)         ('{d_1\1[],d_2\1[]}),
    );
    */
   test_port0
     u0(/*AUTOINST*/
        // Outputs
        .d                                      ('{d_1[31:0],d_2[31:0]})); // Templated
   
   /*
    test_port1  AUTO_TEMPLATE
    (
    .d\(.*\)         ('{d_1\1[],d_2\1[]}),
    );
    */
   
   test_port1
     u1(/*AUTOINST*/
        // Inputs
        .dd                             ('{d_1d[31:0],d_2d[31:0]})); // Templated
endmodule // top


