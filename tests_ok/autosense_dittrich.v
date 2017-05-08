module testcase
  (/*AUTOARG*/
   // Outputs
   Z,
   // Inputs
   A, B, C, D, SEL
   );
   
   input       A, B, C, D;
   input [1:0] SEL;
   output      Z;
   
`include autosense_dittrich_inc.v
   
   always @(/*AS*/A or B or C or D or SEL) begin
      case (SEL)
        sel_a: Z   = A;
        sel_b: Z   = B;
        sel_c: Z   = C;
        sel_d: Z   = D;
        default: Z = D;
      endcase // case(SEL)
   end // always @ (...
   
endmodule // testcase

// Local Variables:
// verilog-auto-read-includes:t
// End:
