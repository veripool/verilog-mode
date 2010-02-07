module autoinoutmodule (
                        /*AUTOINOUTMODULE("inst")*/
                        // Beginning of automatic in/out/inouts (from specific module)
                        output lower_out,
                        input  lower_inb,
                        input  lower_ina
                        // End of automatics
                        );
   
   wire lower_out = lower_ina | lower_inb;
   
endmodule

