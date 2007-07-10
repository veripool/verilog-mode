module autoinstparam_first ();

   parameter BITSA;
   parameter BITSB;

   autoinstparam_first_sub
     #(/*AUTOINSTPARAM*/
       // Parameters
       .BITSA				(BITSA),
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
       .BITSA				(BITSA))
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

endmodule
