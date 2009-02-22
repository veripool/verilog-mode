module temp2(/*AUTOARG*/);
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [5:0] out;                      // From adc_3 of adc.v
   // End of automatics
   
   adc adc_3 (
              // Outputs
              .out                      (out[5:0]),
              // Inputs
              .Vi                       (Vi),
              // Inputs
              .evalClk                  (evalClk),
              /*AUTOINST*/);
   
endmodule // temp


module adc(/*AUTOARG*/
           // Outputs
           out,
           // Inputs
           Vi, evalClk
           );
   output [5:0] out;
   input        Vi;
   input        evalClk;
endmodule
