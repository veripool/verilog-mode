module autotieoff_signed (/*AUTOARG*/);

   input [2:0]		ExtraIn;
   output [2:0] 	ExtraOut;
   output [3:0] 	active_low_l;

   /*AUTOINOUTMODULE("autoinst_signed")*/

   // =============================
   // Auto Wires/Regs
   // =============================

   /*AUTOWIRE*/
   /*AUTOREG*/

   // =============================
   // Tieoffs
   // =============================

   /*AUTOTIEOFF*/

   // =============================
   // Unused signals
   // =============================

   // lint_checking SCX_UNUSED OFF
   wire _unused_ok = &{1'b0,
		       /*AUTOUNUSED*/
		       1'b0};
   // lint_checking SCX_UNUSED OFF

endmodule

// Local Variables:
// verilog-active-low-regexp: "_l$"
// End:
