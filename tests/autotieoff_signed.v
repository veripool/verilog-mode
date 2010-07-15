module autotieoff_signed (/*AUTOARG*/);

   input [2:0]		ExtraIn;
   input [2:0]		SubIn;
   output [2:0] 	ExtraOut;
   output [2:0] 	SubOut;
   output [3:0] 	active_low_l;
   output [3:0] 	ignored_by_regexp;

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
   
   sub sub (/*AUTOINST*/);

   // =============================
   // Unused signals
   // =============================

   // lint_checking SCX_UNUSED OFF
   wire _unused_ok = &{1'b0,
		       /*AUTOUNUSED*/
		       1'b0};
   // lint_checking SCX_UNUSED OFF

endmodule

module sub;
   input SubIn;
   output SubOut;
endmodule

// Local Variables:
// verilog-active-low-regexp: "_l$"
// verilog-auto-tieoff-ignore-regexp: "ignored"
// End:
