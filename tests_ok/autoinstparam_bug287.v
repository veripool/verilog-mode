module Ptest #(
               parameter I_CONTROL = 8'h 00, R_CONTROL = 8'h00)
   (
    input scanTest,
    input scanArst);
endmodule

module t;
   
   Ptest
     #(/*AUTOINSTPARAM*/
       // Parameters
       .I_CONTROL                       (I_CONTROL),
       .R_CONTROL                       (R_CONTROL))
   u_Ptest
     (/*AUTOINST*/
      // Inputs
      .scanTest                         (scanTest),
      .scanArst                         (scanArst));
   
endmodule
