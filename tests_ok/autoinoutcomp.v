module autoinoutmodule (/*AUTOARG*/
                        // Outputs
                        lower_ina, lower_inb,
                        // Inputs
                        lower_out
                        );
   
   output lower_inb;
   
   /*AUTOINOUTCOMP("inst")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output lower_ina;
   input  lower_out;
   // End of automatics
   // Beginning of automatic in/out/inouts (from specific module)
   
   wire   lower_out = lower_ina | lower_inb;
   
endmodule

