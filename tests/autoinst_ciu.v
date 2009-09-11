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
     (/*AUTOINST*/);

   testmux foo1_2
     (/*AUTOINST*/);

endmodule
