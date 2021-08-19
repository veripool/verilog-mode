module test
  (/*AUTOARG*/);
   
   parameter            WIDTH = 16;
   
   // ISSUE: in autowire below [WIDTH*0-1:0] should have been [WIDTH*2/8-1:0]
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [WIDTH*2/8-1:0] signal;                 // From subtestout of subtestout.v
   // End of automatics
   
   subtestin #(.WIDTH(WIDTH)) subtestin
     (/*AUTOINST*/
      // Inputs
      .signal                           (signal[WIDTH*2/8-1:0]));
   
   
   subtestout #(.WIDTH(WIDTH)) subtestout
     (/*AUTOINST*/
      // Outputs
      .signal                           (signal[WIDTH*2/8-1:0]));
   
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
