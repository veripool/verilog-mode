// $Id: tss_max32.v,v 1.6 1999/01/20 17:34:54 wsnyder Exp $
//============================================================================

`time_scale

module tss_max32 (/*AUTOARG*/
                  // Outputs
                  max,
                  // Inputs
                  a, b
                  );
   
   //======================================================================
   // Inputs/Outputs
   //======================================================================
   
   input [31:0]  a; // Time a
   input [31:0]  b; // Time b
   output [31:0] max; // MAX (a,b)
   
   //======================================================================
   // Automatic Wire/Register Declarations
   //======================================================================
   
   /*AUTOREG*/
   
   //======================================================================
   // Comparison
   //======================================================================
   
   wire          alessb;        // a<b or carry
   //Verilint 110 off // WARNING: Incompatible width
   DW01_cmp2 #(31) cmp (.LT_LE(alessb), .GE_GT(unused_ok),
                        .A(a[30:0]),
                        .B(b[30:0]),
                        .LEQ(1'b0), .TC(1'b0));
   //Verilint 110 on  // WARNING: Incompatible width
   
   // Note because a has more bits we MUST choose it if a[31:8]==b[31:8]!
   wire        sela = ((a[31] != b[31]) ^ alessb);
   wire [31:0] max = (sela ? b : a);
   
endmodule
