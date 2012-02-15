module foo (/*AUTOARG*/) ;
  /*AUTOINPUT("ab\(c\|d\)")*/
  bar i_bar(/*AUTOINST*/);

endmodule // foo

module bar (/*AUTOARG*/) ;
  input abc,abd,bca;
  output aaa;
endmodule // bar
