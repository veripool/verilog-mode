module autoinst_vkadamby ( /*AUTOARG*/);
   
   child1 #(.lengthM2(100))  I34 (/*AUTOINST*/
                                  // Inputs
                                  .x                    (x));
   
endmodule

module child1 (/*AUTOARG*/
               // Inputs
               x
               );
   
   input     x;
   parameter lengthM2;
   
endmodule

