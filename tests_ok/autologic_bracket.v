module sub1
  #(
    parameter integer AAA= {32'd4,32'd8},
    parameter integer BBB= 1
    )
   (
    output [AAA[BBB] -1:0] out_signal
    );
endmodule

module top
  #(
    parameter integer AAA = {32'd4,32'd8},
    parameter integer BBB = 1
    )
   (
    );
   
   /*AUTOLOGIC*/
   
   logic [AAA[BBB] -1:0] out_signal;             // From sub1 of sub1.v
   
   sub1 #(/*AUTOINSTPARAM*/
          // Parameters
          .AAA                          (AAA),
          .BBB                          (BBB))
   sub1 (/*AUTOINST*/
         // Outputs
         .out_signal                    (out_signal[(AAA)[BBB]-1:0]));
   
   
endmodule
