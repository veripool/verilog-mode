module aaa (/*AUTOARG*/
            // Outputs
            y1, y0, u1, u0,
            // Inputs
            y3, y2
            );
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output u0; // From bbb of bbb.v
   output u1; // From bbb of bbb.v
   output y0; // From bbb of bbb.v
   output y1; // From bbb of bbb.v
   // End of automatics
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input  y2; // To bbb of bbb.v
   input  y3; // To bbb of bbb.v
   // End of automatics
   /*AUTOWIRE*/
   
   wire   u0, u1, z0, z1;
   /*
    bbb AUTO_TEMPLATE (
    .xo0 ({(u0), y0}),
    .xo1 ({y1, (u1)}),
    .xi0 ({(z0), y2}),
    .xi1 ({y3, (z1)}),
    );
    */
   bbb bbb (/*AUTOINST*/
            // Outputs
            .xo0                        ({(u0), y0}),            // Templated
            .xo1                        ({y1, (u1)}),            // Templated
            // Inputs
            .xi0                        ({(z0), y2}),            // Templated
            .xi1                        ({y3, (z1)}));           // Templated
   
endmodule // aaa

module bbb (/*AUTOARG*/
            // Outputs
            xo0, xo1,
            // Inputs
            xi0, xi1
            );
   output [1:0] xo0, xo1;
   input [1:0]  xi0, xi1;
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   wire [1:0]   xo0 = 2'h0;
   wire [1:0]   xo1 = 2'h0;
   // End of automatics
endmodule // bbb
