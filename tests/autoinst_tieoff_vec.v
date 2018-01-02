module autotieoff_signed (/*AUTOARG*/);

   /*AUTO_LISP(setq my-nc-output "\/*NC*\/"  my-nc-input-scalar "1'b0"   my-nc-input-vector "'0"  my-nc-input-mdv "'{default:'0}"  my-space "|")*/

     /* sub AUTO_TEMPLATE (
       .\(.*\)    (@"(concat (if (equal vl-dir \\"output\\") my-nc-output  (if (not vl-memory) my-nc-input-vector  my-nc-input-mdv) )  my-space vl-width my-space vl-bits my-space vl-mbits my-space vl-memory )"),
	) */

   // Value | vl-width | vl-bits | vl-mbits | vl-memory
   sub sub (/*AUTOINST*/
	    // Outputs
	    .outvar			(/*NC*/|1|||),		 // Templated
	    // Inputs
	    .scalar_var			('0|1|||),		 // Templated
	    .packed1_var		('0|2|[1:0]||),		 // Templated
	    .packed2_var		('0|3|[2:0]|[1:0]|),	 // Templated
	    .packed1_unpacked1_var	('{default:'0}|2|[1:0]||[2]), // Templated
	    .packed1_unpacked2_var	('{default:'0}|2|[1:0]||[2][3]), // Templated
	    .packed2_unpacked1_var	('{default:'0}|3|[2:0]|[1:0]|[2]), // Templated
	    .packed2_unpacked2_var	('{default:'0}|3|[2:0]|[1:0]|[2][3]), // Templated
	    .unpacked1_var		('{default:'0}|1|||[2]), // Templated
	    .unpacked2_var		('{default:'0}|1|||[2][3])); // Templated

endmodule

module sub
  (
   output outvar,
   input wire 		 scalar_var,
   input wire [1:0] 	 packed1_var,
   input wire [1:0][2:0] packed2_var,
   input wire [1:0] 	 packed1_unpacked1_var [2],
   input wire [1:0] 	 packed1_unpacked2_var [2][3],
   input wire [1:0][2:0] packed2_unpacked1_var [2],
   input wire [1:0][2:0] packed2_unpacked2_var [2][3],
   input wire 		 unpacked1_var [2]
   input wire 		 unpacked2_var [2][3]
   );
endmodule

// Local Variables:
// verilog-active-low-regexp: "_l$"
// verilog-auto-tieoff-ignore-regexp: "ignored"
// End:
