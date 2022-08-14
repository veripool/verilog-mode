module Sub ();
   input a;
endmodule

module t ();

   /* Sub AUTO_TEMPLATE(
       .unused (x));
    */

   Sub sub (/*AUTOINST*/
	    // Inputs
	    .a				(a));

endmodule

// Local Variables:
// verilog-warn-fatal: t
// End:
