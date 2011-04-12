module InstMod ( ins, outs );
    output [INWIDTH-1:0] ins;
    output [OUTWIDTH-1:0] outs;
endmodule

module test_top;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [n*INWIDTH  +: INWIDTH] ins;		// From instName of InstMod.v
   wire [n*INWIDTH  +: INWIDTH] ins2;		// From instName2 of InstMod.v
   wire [n*INWIDTH  +: INWIDTH] ins3;		// From instName3 of InstMod.v, ..., Couldn't Merge
   wire [n*OUTWIDTH +: OUTWIDTH] outs;		// From instName of InstMod.v
   wire [n*OUTWIDTH +: OUTWIDTH] outs2;		// From instName2 of InstMod.v
   wire [4*OUTWIDTH-1 : 0] outs3;		// From instName3 of InstMod.v, ..., Couldn't Merge
   // End of automatics

   genvar i;
   generate
      for (i=0; i<4; i=i+1) begin
	 /*AUTO_LISP(setq vh-n 4)*/
	 /* InstMod AUTO_TEMPLATE
	     (.ins    (ins [n*INWIDTH  +: INWIDTH]),
	      .outs   (outs[n*OUTWIDTH +: OUTWIDTH])); */

	 InstMod instName (/*AUTOINST*/
			   // Outputs
			   .ins			(ins [n*INWIDTH  +: INWIDTH]), // Templated
			   .outs		(outs[n*OUTWIDTH +: OUTWIDTH])); // Templated

	 InstMod instName2
	     (// Inputs
	      .ins    (ins2 [n*INWIDTH  +: INWIDTH]),
	      // Outputs
	      .outs   (outs2[n*OUTWIDTH +: OUTWIDTH])
	      /*AUTOINST*/);

	 // This works but is ugly
	 InstMod instName3
	     (// Inputs
	      .ins    (ins3 [n*INWIDTH  +: INWIDTH]),
	      // Outputs
	      .outs   (outs3[n*OUTWIDTH +: OUTWIDTH])
`ifdef NEVER
	      // Inouts
	      .ins    (ins3 [4*INWIDTH-1  : 0]),
	      .outs   (outs3[4*OUTWIDTH-1 : 0])
`endif
	      /*AUTOINST*/);

      end
   endgenerate
endmodule
