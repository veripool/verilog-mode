module  testmux();
   # (parameter WIDTH = 32)
   (
    input wire [2:0]    /* synopsys enum cur_info */ sel,
    input wire [WIDTH-1:0] a,
    output reg [WIDTH-1:0] out
    );
endmodule

module  top_test();

   /*AUTOWIRE*/

   /*AUTO_LISP(setq verilog-auto-inst-param-value nil)*/

   /* testmux AUTO_TEMPLATE "testmux_\(.*\)" (
    .a (@_a_symbolic[]),
    .out (@_out_symbolic[]),
    );
    */

   testmux #(.WIDTH(  16  )) testmux_boo
     (/*AUTOINST*/);

   testmux  testmux_defaultwidth
     (/*AUTOINST*/);

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
       (/*AUTOINST*/);

   //======================================================================

   testmux #(.IGNORE((1)),
	     .WIDTH(WIDTH),   // Make sure we don't recurse!
	     .IGNORE2(2))
     testmux_boo
       (/*AUTOINST*/);

endmodule
