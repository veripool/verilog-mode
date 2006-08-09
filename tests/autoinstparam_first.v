module autoinstparam_first ();

   parameter BITSA;
   parameter BITSB;

   autoinstparam_first_sub sub
     #(/*AUTOINSTPARAM*/)
       (/*AUTOINST*/);

   autoinstparam_first_sub sub1
     #(
       .BITSB				(2)
       /*AUTOINSTPARAM*/)
       (/*AUTOINST*/);

   autoinstparam_first_sub sub2
     #(
       .BITSA				(1),
       .BITSB				(2)
       /*AUTOINSTPARAM*/)
       (/*AUTOINST*/);

endmodule
