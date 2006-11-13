module autoinstparam_first ();

   parameter BITSA;
   parameter BITSB;

   autoinstparam_first_sub
     #(/*AUTOINSTPARAM*/)
       sub
	 (/*AUTOINST*/);

   autoinstparam_first_sub
     #(
       .BITSB				(2)
       /*AUTOINSTPARAM*/)
       sub1
	 (/*AUTOINST*/);

   autoinstparam_first_sub
     #(
       .BITSA				(1),
       .BITSB				(2)
       /*AUTOINSTPARAM*/)
       sub2
	 (/*AUTOINST*/);

endmodule
