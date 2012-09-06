module autoinoutmodule (/*AUTOARG*/
                        // Outputs
                        lower_out,
                        // Inputs
                        lower_ina
                        );
   
   /*AUTOINOUTMODULE("inst","\(ina\|out\)")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output lower_out;
   input  lower_ina;
   // End of automatics
   
   wire   lower_out = lower_ina;
   
endmodule

