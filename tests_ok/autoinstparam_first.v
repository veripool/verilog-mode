module autoinstparam_first ();

   parameter BITSA;
   parameter BITSB;

   autoinstparam_first_sub sub
     #(/*AUTOINSTPARAM*/
       // Parameters
       .BITSA				(BITSA),
       .BITSB				(BITSB))
       (/*AUTOINST*/
	// Inouts
	.a				(a[BITSA:0]),
	.b				(b[BITSB:0]));

   autoinstparam_first_sub sub1
     #(
       .BITSB				(2)
       /*AUTOINSTPARAM*/
       // Parameters
       .BITSA				(BITSA))
       (/*AUTOINST*/
	// Inouts
	.a				(a[BITSA:0]),
	.b				(b[BITSB:0]));

   autoinstparam_first_sub sub2
     #(
       .BITSA				(1),
       .BITSB				(2)
       /*AUTOINSTPARAM*/)
       (/*AUTOINST*/
	// Inouts
	.a				(a[BITSA:0]),
	.b				(b[BITSB:0]));

endmodule
