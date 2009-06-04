module aaa (/*AUTOARG*/);

   /*AUTOOUTPUT*/
   /*AUTOINPUT*/
   /*AUTOWIRE*/

   wire u0, u1, z0, z1;
   /*
    bbb AUTO_TEMPLATE (
            .xo0 ({(u0), y0}),
            .xo1 ({y1, (u1)}),
            .xi0 ({(z0), y2}),
            .xi1 ({y3, (z1)}),
    );
    */
   bbb bbb (/*AUTOINST*/);

endmodule // aaa

module bbb (/*AUTOARG*/);
   output [1:0] xo0, xo1;
   input [1:0]  xi0, xi1;
   /*AUTOTIEOFF*/
endmodule // bbb
