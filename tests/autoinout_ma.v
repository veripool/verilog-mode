module foo
  (
   input  soutb,
   output sina,

   /*AUTOINPUT*/
   /*AUTOOUTPUT*/
   ) ;
  bar i_bar(/*AUTOINST*/);

endmodule // foo

module bar (/*AUTOARG*/) ;
   input sina, sinb;
   output souta, soutb;
endmodule // bar
