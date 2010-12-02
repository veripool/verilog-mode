module TOP (/*AUTOARG*/)
  /*AUTOOUTPUT*/
  /*AUTOINPUT*/
  /*AUTOWIRE*/

  A A(/*AUTOINST*/);
   B B(/*AUTOINST*/);
endmodule

module A(/*AUTOARG*/);
   output [224*1-1:128*1] SIG_NAMEA;
   //output [223:128] SIG_NAMEA;
endmodule


module B(/*AUTOARG*/);
   output [127:0] SIG_NAMEA;
endmodule


