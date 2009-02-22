module lbnsub
  (/*AUTOARG*/
   // Outputs
   outgo,
   // Inputs
   income
   );
   
   input [7:4]  income;
   output [7:4] outgo;
   
   wire [7:4]   outgo = income;
   
endmodule

module lbm
  (/*AUTOARG*/
   // Outputs
   outgo,
   // Inputs
   income
   );
   
   input [7:4]  income;
   output [7:4] outgo;
   
   /*
    lbnsub AUTO_TEMPLATE (
    // Inputs
    .income     (income[4:7]));
    */
   
   lbnsub lbnsub        (/*AUTOINST*/
                         // Outputs
                         .outgo                 (outgo[7:4]),
                         // Inputs
                         .income                (income[4:7]));  // Templated
endmodule

