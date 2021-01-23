module test
  (/*AUTOARG*/);

   parameter WIDTH = 16;
  
   // ISSUE: in autowire below [WIDTH*0-1:0] should have been [WIDTH*2/8-1:0]

   /*AUTOWIRE*/

   subtestin #(.WIDTH(WIDTH)) subtestin
     (/*AUTOINST*/);

   
   subtestout #(.WIDTH(WIDTH)) subtestout
     (/*AUTOINST*/);

endmodule

module subtestin
  #(parameter WIDTH=0)
  (input wire [WIDTH*2/8-1:0] signal
   /*AUTOARG*/);
endmodule

module subtestout
  #(parameter WIDTH=0)
  (output wire [WIDTH*2/8-1:0] signal
   /*AUTOARG*/);
   assign signal = 0;
endmodule
