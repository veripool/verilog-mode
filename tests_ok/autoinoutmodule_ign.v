module autoinoutmodule (/*AUTOARG*/
                        // Outputs
                        lower_out
                        );
   
   /*AUTOINOUTMODULE("inst","\(ina\|out\)","","ina")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output lower_out;
   // End of automatics
   
   wire   lower_out = lower_ina;
   
endmodule

