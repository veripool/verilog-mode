module autotieoff_signed (/*AUTOARG*/
   // Outputs
   an_output2, an_outputpre, another_output, another_output2, ExtraOut, active_low_l,
   // Inputs
   ExtraIn
   );

   input [2:0]		ExtraIn;
   output [2:0] 	ExtraOut;
   output [3:0] 	active_low_l;

   /*AUTOINOUTMODULE("autoinst_signed")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output [1:0]		an_output2;
   output signed [1:0]	an_outputpre;
   output signed [1:0]	another_output;
   output [1:0]		another_output2;
   // End of automatics

   // =============================
   // Auto Wires/Regs
   // =============================

   /*AUTOWIRE*/
   /*AUTOREG*/

   // =============================
   // Tieoffs
   // =============================

   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   wire [2:0]		ExtraOut		= 3'h0;
   wire [3:0]		active_low_l		= ~4'h0;
   wire [1:0]		an_output2		= 2'h0;
   wire signed [1:0]	an_outputpre		= 2'sh0;
   wire signed [1:0]	another_output		= 2'sh0;
   wire [1:0]		another_output2		= 2'h0;
   // End of automatics

   // =============================
   // Unused signals
   // =============================

   // lint_checking SCX_UNUSED OFF
   wire _unused_ok = &{1'b0,
		       /*AUTOUNUSED*/
		       // Beginning of automatic unused inputs
		       ExtraIn,
		       // End of automatics
		       1'b0};
   // lint_checking SCX_UNUSED OFF

endmodule

// Local Variables:
// verilog-active-low-regexp: "_l$"
// End:
