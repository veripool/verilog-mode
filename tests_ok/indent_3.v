module junk (/*AUTOARG*/
             // Outputs
             c_junk, d_junk,
             // Inputs
             a_junk, b_junk
             ) ;
   input                                          a_junk;
   input wire signed [15:0]                       b_junk;
   output                                         c_junk;
   output [15:0][31:0][1024:(`REALLY_BIG_NAME-1)] d_junk;
endmodule // junk

