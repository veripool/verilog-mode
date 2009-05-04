module top
  (input [(`WIDTH):0] a, /* This comma gets deleted */
   /*AUTOOUTPUT*/
   /*AUTOINPUT*/
   );
   
   child child(/*AUTOINST*/);
endmodule

module nocomma
  (/*AUTOOUTPUT*/
   /*AUTOINPUT*/
   );
   child child(/*AUTOINST*/);
endmodule

module ifdefcomma
  (
`ifdef a
   input foo,
`endif
   /*AUTOOUTPUT*/
   /*AUTOINPUT*/
   );
   child child(/*AUTOINST*/);
endmodule

module ifdefnocomma
  (
`ifdef a
   // It's up to the user to deal with the , themself
   input foo,
`endif
   /*AUTOOUTPUT*/
   );
   child child(/*AUTOINST*/);
endmodule

module child(input b);
endmodule
