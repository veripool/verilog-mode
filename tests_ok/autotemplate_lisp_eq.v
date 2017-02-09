module test1 ( wire2, wire4 );
   output [3:0]  wire2;
   output [16:0] wire4;
endmodule

// msg2099

module test_top;
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire        eq; // From test_rcv of test1.v
   wire        not_eq; // From test_foo of test1.v
   wire [16:0] wire4;                   // From test_rcv of test1.v, ...
   // End of automatics
   
   /*
    .wire2   (@"(if (equal \\"@\\" \\"rcv\\") \\"eq\\" \\"not_eq\\" )"),
    */
   
   /* test1 AUTO_TEMPLATE "test_\(.*\)" (
    .wire2\(\) (@"(if (equal \\"@\\" \\"rcv\\") \\"eq\\" \\"not_eq\\" )"),
    ); */
   
   test1 test_rcv (/*AUTOINST*/
                   // Outputs
                   .wire2               (eq),                    // Templated
                   .wire4               (wire4[16:0]));
   
   test1 test_foo (/*AUTOINST*/
                   // Outputs
                   .wire2               (not_eq),                // Templated
                   .wire4               (wire4[16:0]));
   
endmodule
