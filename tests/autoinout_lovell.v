// Matthew Lovell <lovell@hp.com>

module top_test(/*AUTOARG*/);

   /*AUTOOUTPUT*/

   /*AUTOINPUT*/

   /* leaf AUTO_TEMPLATE (
    // Original reported bug
    .a  ({aa, test2.test3.no, test3.test4.no2}),
    // Others
    .b  ( ~ ba),
    .c  ({\c-escaped-nvec , \c-escaped-vec [2:0] }),
    .d  ({da,~ db [1:0] , dc [2:0]}),
    // Msg246
    .e ({{4*1{1'b0}},Z_int[15:0],{1'b4{1'b0}},Z0_int[7:0]}),
    .f (hi.ear.ial),
    );
    */
   leaf l1 (/*AUTOINST*/);
endmodule // top_test

module leaf(/*AUTOARG*/);
   output a;
   output  b;
   input c;
   input d;
   input e;
   input f;
   input z;
endmodule
