module autoinoutmodule (/*AUTOARG*/
   // Outputs
   lower_out,
   // Inputs
   lower_inb, lower_ina
   );

   /*AUTOINOUTMODULE("inst")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output		lower_out;
   input		lower_inb;
   input		lower_ina;
   // End of automatics
   // Beginning of automatic in/out/inouts (from specific module)

   wire   lower_out = lower_ina | lower_inb;

endmodule

