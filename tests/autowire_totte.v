module test1 ( wire2, wire4 );
    output [3:0] wire2;
    output [16:0] wire4;
endmodule

module test2 ( wire6, wire12 );
    input [3:0] wire6;
    input [16:0] wire12;
endmodule

module test3 ( wireA, wireB );
    input [3:0] wireA;
    input [16:0] wireB;
endmodule

module test4 ( wireA, wireB );
    output [3:0] wireA;
    output [16:0] wireB;
endmodule

module test_top;

    /*AUTOWIRE*/

    /* test1 AUTO_TEMPLATE (
        .wire@(wire_\1_to_@"(* \1 3)"[]),
    ); */

    test1 t1 (/*AUTOINST*/);

    /* test2 AUTO_TEMPLATE (
        .wire@(wire@"(/ \1 3)"_to_\1[]),
    ); */

    test2 t2 (/*AUTOINST*/);

    test3 t3 (/*AUTOINST*/);

    test4 t4 (/*AUTOINST*/);

endmodule
