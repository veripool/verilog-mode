module foo();
   bar i0 (
           /*AUTOINST*/
           );
endmodule // foo

module bar(input logic a);
`pragma protect begin_protected
`pragma protect data_block
   AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA[
`pragma protect end_protected
endmodule // bar
