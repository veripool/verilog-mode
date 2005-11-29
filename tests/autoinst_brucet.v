module io1_sub(/*AUTOARG*/
   // Outputs
   x, y, z,
   // Inputs
   a, b
   );

   input a;
   input b;
   output x;
   output y;
   output z;

   andcell c0 (
	       .c			(x),
	       /*AUTOINST*/
	       // Inputs
	       .a			(a),
	       .b			(b));

   orcell c0 (
	      .c			(y),
	      /*AUTOINST*/
	      // Inputs
	      .a			(a),
	      .b			(b));

   nandcell c0 (
		.c			(z),
		/*AUTOINST*/
		// Inputs
		.a			(a),
		.b			(b));

endmodule

// Local Variables:
// verilog-library-files:("autoinst_brucet_library.v")
// End:
