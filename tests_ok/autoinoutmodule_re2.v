module autoinoutmodule_re2 (/*AUTOARG*/
                            // Outputs
                            lower_out,
                            // Inputs
                            lower_inb, lower_ina
                            );
   
   /*AUTOINOUTMODULE("inst","","input.*")*/
   // Beginning of automatic in/out/inouts (from specific module)
   input  lower_inb;
   input  lower_ina;
   // End of automatics
   
   /*AUTOINOUTMODULE("inst","","output.*")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output lower_out;
   // End of automatics
   
   wire   lower_out = lower_ina;
   
endmodule

