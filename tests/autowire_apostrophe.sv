module test_port0
(/*AUTOARG*/);
    output [31:0] d[2];
endmodule // test_port

module test_port1
(/*AUTOARG*/);
   input [31:0] dd[2];
endmodule // test_port1

module top()
/*AUTOWIRE*/

/*
   test_port0  AUTO_TEMPLATE
   (
   .d\(.*\)         ('{d_1\1[],d_2\1[]}),
   );
*/
test_port0
  u0(/*AUTOINST*/);

  /*
   test_port1  AUTO_TEMPLATE
   (
   .d\(.*\)         ('{d_1\1[],d_2\1[]}),
   );
*/

test_port1
  u1(/*AUTOINST*/);

endmodule // top
