module autotieoff_signed (/*AUTOARG*/
                          // Outputs
                          an_output2, an_outputpre, another_output, another_output2, ExtraOut, SubOut, active_low_l,
                          ignored_by_regexp,
                          // Inputs
                          ExtraIn, SubIn
                          );
   
   input [2:0]         ExtraIn;
   input [2:0]         SubIn;
   output [2:0]        ExtraOut;
   output [2:0]        SubOut;
   output [3:0]        active_low_l;
   output [3:0]        ignored_by_regexp;
   
   /*AUTOINOUTMODULE("autoinst_signed")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output [1:0]        an_output2;
   output signed [1:0] an_outputpre;
   output signed [1:0] another_output;
   output [1:0]        another_output2;
   // End of automatics
   
   // =============================
   // Auto Wires/Regs
   // =============================
   
   /*AUTOWIRE*/
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [3:0]           ignored_by_regexp;
   // End of automatics
   
   // =============================
   // Tieoffs
   // =============================
   
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   wire [2:0]          ExtraOut = 3'h0;
   wire [3:0]          active_low_l = ~4'h0;
   wire [1:0]          an_output2 = 2'h0;
   wire signed [1:0]   an_outputpre = 2'sh0;
   wire signed [1:0]   another_output = 2'sh0;
   wire [1:0]          another_output2 = 2'h0;
   // End of automatics
   
   // =============================
   
   sub sub (/*AUTOINST*/
            // Outputs
            .SubOut                     (SubOut),
            // Inputs
            .SubIn                      (SubIn));
   
   // =============================
   // Unused signals
   // =============================
   
   // lint_checking SCX_UNUSED OFF
   wire _unused_ok = &{1'b0,
                       /*AUTOUNUSED*/
                       // Beginning of automatic unused inputs
                       ExtraIn,
                       // End of automatics
                       1'b0 } ;
   // lint_checking SCX_UNUSED OFF
   
endmodule

module sub;
   input  SubIn;
   output SubOut;
endmodule

// Local Variables:
// verilog-active-low-regexp: "_l$"
// verilog-auto-tieoff-ignore-regexp: "ignored"
// End:
