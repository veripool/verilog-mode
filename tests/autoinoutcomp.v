module autoinoutmodule (/*AUTOARG*/);

   output lower_inb;

   /*AUTOINOUTCOMP("inst")*/
   // Beginning of automatic in/out/inouts (from specific module)

   wire   lower_out = lower_ina | lower_inb;

endmodule

