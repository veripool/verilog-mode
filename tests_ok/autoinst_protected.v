module foo();
   bar i0 (
           /*AUTOINST*/
           // Inputs
           .a                           (a));
endmodule // foo

module bar(input logic a);
   `protected
     input            notreally;
   `endprotected
     
`pragma protect begin_protected
`pragma protect data_block
     AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA[
`pragma protect end_protected
                                                                                 
                                                                                 endmodule // bar
