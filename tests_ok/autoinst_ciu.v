module  testmux
  (
   input wire [2:0] a
   );
endmodule

module  top_test();
   
   /* testmux AUTO_TEMPLATE "\(.*\)$" (
    .a (@_a_value[]),
    );
    */
   
   testmux foo1_1
     (/*AUTOINST*/
      // Inputs
      .a                                (foo1_1_a_value[2:0]));  // Templated
   
   testmux foo1_2
     (/*AUTOINST*/
      // Inputs
      .a                                (foo1_2_a_value[2:0]));  // Templated
   
endmodule
