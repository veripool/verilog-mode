module test1 ( wire2, wire4 );
   output [3:0]  wire2;
   output [16:0] wire4;
endmodule

module test2 ( wire6, wire12 );
   input [3:0]  wire6;
   input [16:0] wire12;
endmodule

module test3 ( wireA, wireB );
   input [3:0]  wireA;
   input [16:0] wireB;
endmodule

module test4 ( wireA, wireB );
   output [3:0]  wireA;
   output [16:0] wireB;
endmodule

module test_top;
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]  wireA; // From t4 of test4.v
   wire [16:0] wireB; // From t4 of test4.v
   wire [3:0]  wire_2_to_6; // From t1 of test1.v
   wire [16:0] wire_4_to_12;            // From t1 of test1.v
   // End of automatics
   
   /* test1 AUTO_TEMPLATE (
    .wire@(wire_\1_to_@"(* \1 3)"[]),
    ); */
   
   test1 t1 (/*AUTOINST*/
             // Outputs
             .wire2                     (wire_2_to_6[3:0]),      // Templated
             .wire4                     (wire_4_to_12[16:0]));   // Templated
   
   /* test2 AUTO_TEMPLATE (
    .wire@(wire@"(/ \1 3)"_to_\1[]),
    ); */
   
   test2 t2 (/*AUTOINST*/
             // Inputs
             .wire6                     (wire2_to_6[3:0]),       // Templated
             .wire12                    (wire4_to_12[16:0]));    // Templated
   
   test3 t3 (/*AUTOINST*/
             // Inputs
             .wireA                     (wireA[3:0]),
             .wireB                     (wireB[16:0]));
   
   test4 t4 (/*AUTOINST*/
             // Outputs
             .wireA                     (wireA[3:0]),
             .wireB                     (wireB[16:0]));
   
endmodule
