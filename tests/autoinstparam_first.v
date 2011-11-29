module autoinstparam_first ();

   parameter BITSCHANGED;
   parameter BITSA;
   parameter type BITSB_t;
   typedef [2:0] my_bitsb_t;

   /* autoinstparam_first_sub AUTO_TEMPLATE (
       .BITSA		(BITSCHANGED),
    ); */

   autoinstparam_first_sub
     #(/*AUTOINSTPARAM*/)
       sub
	 (/*AUTOINST*/);

   autoinstparam_first_sub
     #(
       .BITSB_t				(my_bitsb_t),
       /*AUTOINSTPARAM*/)
       sub1
	 (/*AUTOINST*/);

   autoinstparam_first_sub
     #(
       .BITSA				(1),
       .BITSB_t				(my_bitsb_t)
       /*AUTOINSTPARAM*/)
       sub2
	 (/*AUTOINST*/);

   autoinstparam_first_sub
     #(
       /*AUTOINSTPARAM*/)
       sub3
	 (/*AUTOINST*/);

endmodule

// Local Variables:
// verilog-auto-inst-param-value:nil
// verilog-typedef-regexp: "_t$"
// End:
