module bug1526;
   /*AUTOINPUT*/
   /*AUTOOUTPUT*/
   /*AUTOWIRE*/
   
   
   wire [3:0][27:0]         x;
   typedef wire [3:0][27:0] t;
   
   /*t2  AUTO_TEMPLATE  (
    .x(x),
    )*/
   t2 #(// Parameters
        .N(4)
        )
   t2 (/*AUTOINST*/
       // Outputs
       .x                               (x));                    // Templated
   
   /*t3  AUTO_TEMPLATE  (
    .x(t'(x)),
    )*/
   t3 #(// Parameters
        .N(4)
        )
   t3 (/*AUTOINST*/
       // Inputs
       .x                               (t'(x)));                // Templated
   
endmodule

module t2 #(
            parameter N=4
            ) (
               output [N-1:0][27:0] x
               );
endmodule

module t3 #(
            parameter N=4
            ) (
               input [N-1:0][27:0] x
               );
endmodule
