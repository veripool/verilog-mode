module top
  (input [(`WIDTH):0] a, /* This comma gets deleted */
   /*AUTOOUTPUT*/
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input b                      // To child of child.v
   // End of automatics
   );
   
   child child(/*AUTOINST*/
               // Inputs
               .b                       (b));
endmodule

module nocomma
  (/*AUTOOUTPUT*/
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input b                      // To child of child.v
   // End of automatics
   );
   child child(/*AUTOINST*/
               // Inputs
               .b                       (b));
endmodule

module ifdefcomma
  (
`ifdef a
   input foo,
`endif
   /*AUTOOUTPUT*/
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input b                      // To child of child.v
   // End of automatics
   );
   child child(/*AUTOINST*/
               // Inputs
               .b                       (b));
endmodule

module ifdefnocomma
  (
`ifdef a
   // It's up to the user to deal with the , themself
   input foo,
`endif
   /*AUTOOUTPUT*/
   );
   child child(/*AUTOINST*/
               // Inputs
               .b                       (b));
endmodule

module child(input b);
endmodule
