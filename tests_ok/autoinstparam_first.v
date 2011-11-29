module autoinstparam_first ();
   
   parameter BITSCHANGED;
   parameter BITSA;
   parameter type BITSB_t;
   typedef [2:0] my_bitsb_t;
   
   /* autoinstparam_first_sub AUTO_TEMPLATE (
    .BITSA              (BITSCHANGED),
    ); */
   
   autoinstparam_first_sub
     #(/*AUTOINSTPARAM*/
       // Parameters
       .BITSA                           (BITSCHANGED),           // Templated
       .BITSB_t                         (BITSB_t))
   sub
     (/*AUTOINST*/
      // Inouts
      .a                                (a[BITSA:0]),
      .b                                (b));
   
   autoinstparam_first_sub
     #(
       .BITSB_t                         (my_bitsb_t),
       /*AUTOINSTPARAM*/
       // Parameters
       .BITSA                           (BITSCHANGED))           // Templated
   sub1
     (/*AUTOINST*/
      // Inouts
      .a                                (a[BITSA:0]),
      .b                                (b));
   
   autoinstparam_first_sub
     #(
       .BITSA                           (1),
       .BITSB_t                         (my_bitsb_t)
       /*AUTOINSTPARAM*/)
   sub2
     (/*AUTOINST*/
      // Inouts
      .a                                (a[BITSA:0]),
      .b                                (b));
   
   autoinstparam_first_sub
     #(
       /*AUTOINSTPARAM*/
       // Parameters
       .BITSA                           (BITSCHANGED),           // Templated
       .BITSB_t                         (BITSB_t))
   sub3
     (/*AUTOINST*/
      // Inouts
      .a                                (a[BITSA:0]),
      .b                                (b));
   
endmodule

// Local Variables:
// verilog-auto-inst-param-value:nil
// verilog-typedef-regexp: "_t$"
// End:
