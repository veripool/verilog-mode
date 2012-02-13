module autoinst_name_bug245 (
                             );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input        \escaped*dot*named ; // To sub of Sub.v
   input logic  clk; // To sub of Sub.v
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [2:0] a_NO; // From sub of Sub.v
   output [1:0] bign2_dotnamed; // From sub of Sub.v
   output       c_dotnamed; // From sub of Sub.v
   output       d_NO; // From sub of Sub.v
   output       etmp_dotnamed; // From sub of Sub.v
   output [3:0] f4_dotnamed; // From sub of Sub.v
   // End of automatics
   
   /*AUTOWIRE*/
   
   wire [3:0]   f4_dotnamed;
   
   /*Sub AUTO_TEMPLATE (
    .dtmp_NO (d_NO),
    .etmp_dotnamed (etmp_dotnamed),
    );*/
   
   Sub sub (
            .bign1_dotnamed,
            // Outputs
            .bign2_dotnamed,
            /*AUTOINST*/
            // Outputs
            .a_NO                       (a_NO[2:0]),
            .f4_dotnamed,
            .c_dotnamed,
            .dtmp_NO                    (d_NO),                  // Templated
            .etmp_dotnamed,                                      // Templated
            // Inputs
            .clk,
            .\escaped*dot*named );
   
endmodule

module Sub
  (
   input logic  clk,
   output [2:0] a_NO,
   output [3:0] f4_dotnamed,
   output       bign1_dotnamed,
   output [1:0] bign2_dotnamed,
   output       c_dotnamed,
   output       dtmp_NO,
   output       etmp_dotnamed,
   input        \escaped*dot*named
   );
endmodule

// Local Variables:
// verilog-auto-inst-dot-name: t
// verilog-auto-inst-vector: nil
// End:
module autoinst_name_bug245 (
                             );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input        \escaped*dot*named ; // To sub of Sub.v
   input logic  clk; // To sub of Sub.v
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [2:0] a_NO; // From sub of Sub.v
   output [1:0] bign2_dotnamed; // From sub of Sub.v
   output       c_dotnamed; // From sub of Sub.v
   output       d_NO; // From sub of Sub.v
   output       etmp_dotnamed; // From sub of Sub.v
   output [3:0] f4_dotnamed; // From sub of Sub.v
   // End of automatics
   
   /*AUTOWIRE*/
   
   wire [3:0]   f4_dotnamed;
   
   /*Sub AUTO_TEMPLATE (
    .dtmp_NO (d_NO),
    .etmp_dotnamed (etmp_dotnamed),
    );*/
   
   Sub sub (
            .bign1_dotnamed,
            // Outputs
            .bign2_dotnamed,
            /*AUTOINST*/
            // Outputs
            .a_NO                       (a_NO[2:0]),
            .f4_dotnamed,
            .c_dotnamed,
            .dtmp_NO                    (d_NO),                  // Templated
            .etmp_dotnamed,                                      // Templated
            // Inputs
            .clk,
            .\escaped*dot*named );
   
endmodule

module Sub
  (
   input logic  clk,
   output [2:0] a_NO,
   output [3:0] f4_dotnamed,
   output       bign1_dotnamed,
   output [1:0] bign2_dotnamed,
   output       c_dotnamed,
   output       dtmp_NO,
   output       etmp_dotnamed,
   input        \escaped*dot*named
   );
endmodule

// Local Variables:
// verilog-auto-inst-dot-name: t
// verilog-auto-inst-vector: nil
// End:
module autoinst_name_bug245 (
                             );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input        \escaped*dot*named ; // To sub of Sub.v
   input logic  clk; // To sub of Sub.v
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [2:0] a_NO; // From sub of Sub.v
   output [1:0] bign2_dotnamed; // From sub of Sub.v
   output       c_dotnamed; // From sub of Sub.v
   output       d_NO; // From sub of Sub.v
   output       etmp_dotnamed; // From sub of Sub.v
   output [3:0] f4_dotnamed; // From sub of Sub.v
   // End of automatics
   
   /*AUTOWIRE*/
   
   wire [3:0]   f4_dotnamed;
   
   /*Sub AUTO_TEMPLATE (
    .dtmp_NO (d_NO),
    .etmp_dotnamed (etmp_dotnamed),
    );*/
   
   Sub sub (
            .bign1_dotnamed,
            // Outputs
            .bign2_dotnamed,
            /*AUTOINST*/
            // Outputs
            .a_NO                       (a_NO[2:0]),
            .f4_dotnamed,
            .c_dotnamed,
            .dtmp_NO                    (d_NO),                  // Templated
            .etmp_dotnamed,                                      // Templated
            // Inputs
            .clk,
            .\escaped*dot*named );
   
endmodule

module Sub
  (
   input logic  clk,
   output [2:0] a_NO,
   output [3:0] f4_dotnamed,
   output       bign1_dotnamed,
   output [1:0] bign2_dotnamed,
   output       c_dotnamed,
   output       dtmp_NO,
   output       etmp_dotnamed,
   input        \escaped*dot*named
   );
endmodule

// Local Variables:
// verilog-auto-inst-dot-name: t
// verilog-auto-inst-vector: nil
// End:
