module autoinstparam_first ();

   parameter BITSCHANGED;
   parameter BITSA;
   parameter BITSB;

   autoinstparam_first_sub
     #(/*AUTOINSTPARAM*/)
       sub
	 (/*AUTOINST*/);

   autoinstparam_first_sub
     #(
       .BITSB				(2),
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

   /* autoinstparam_first_sub AUTO_TEMPLATE (
       .BITSA		(BITSCHANGED),
    ); */

   autoinstparam_first_sub
     #(
       /*AUTOINSTPARAM*/)
       sub3
	 (/*AUTOINST*/);

endmodule

// Local Variables:
// verilog-auto-inst-param-value:nil
// End:
