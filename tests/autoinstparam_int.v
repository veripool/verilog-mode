module xyz
  #(parameter int FOO=1)
   ( input x, output y); 
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
