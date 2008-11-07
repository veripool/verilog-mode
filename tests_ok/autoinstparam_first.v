module autoinstparam_first ();

   parameter BITSCHANGED;
   parameter BITSA;
   parameter BITSB;

   autoinstparam_first_sub
     #(/*AUTOINSTPARAM*/
       // Parameters
       .BITSA				(BITSCHANGED),		 // Templated
       .BITSB				(BITSB))
       sub
	 (/*AUTOINST*/
	  // Inouts
	  .a				(a[BITSA:0]),
	  .b				(b[BITSB:0]));

   autoinstparam_first_sub
     #(
       .BITSB				(2),
       /*AUTOINSTPARAM*/
       // Parameters
       .BITSA				(BITSCHANGED))		 // Templated
       sub1
	 (/*AUTOINST*/
	  // Inouts
	  .a				(a[BITSA:0]),
	  .b				(b[BITSB:0]));

   autoinstparam_first_sub
     #(
       .BITSA				(1),
       .BITSB				(2)
       /*AUTOINSTPARAM*/)
       sub2
	 (/*AUTOINST*/
	  // Inouts
	  .a				(a[BITSA:0]),
	  .b				(b[BITSB:0]));

   /* autoinstparam_first_sub AUTO_TEMPLATE (
       .BITSA		(BITSCHANGED),
    ); */

   autoinstparam_first_sub
     #(
       /*AUTOINSTPARAM*/
       // Parameters
       .BITSA				(BITSCHANGED),		 // Templated
       .BITSB				(BITSB))
       sub3
	 (/*AUTOINST*/
	  // Inouts
	  .a				(a[BITSA:0]),
	  .b				(b[BITSB:0]));

endmodule

// Local Variables:
// verilog-auto-inst-param-value:nil
// End:
