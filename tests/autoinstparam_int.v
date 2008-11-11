module xyz
  #(parameter int FOO=1, BAR=2,
    parameter logic [5:0] BLUP=3, ZOT=4,
    parameter LDWRDS=5)
   ( input x1, x2,
     input int i1, i2,
     input logic [5:0] i3, i4,
     input i5,
     output y); 
endmodule 

module pdq;
   input x; output y;
   parameter int FOO=1;
endmodule 

module abc; 
   xyz XYZ
     #(/*AUTOINSTPARAM*/)
   (/*AUTOINST*/); 
   pdq PDQ
     #(/*AUTOINSTPARAM*/)
   (/*AUTOINST*/); 
endmodule 
