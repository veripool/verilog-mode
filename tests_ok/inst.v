module inst (/*AUTOARG*/
             // Outputs
             lower_out,
             // Inputs
             lower_inb, lower_ina
             );
   
   parameter param1;
   parameter param2;
   
   input     lower_inb;
   input     lower_ina;
   output    lower_out;
   
   wire      lower_out = lower_ina | lower_inb;
   
endmodule

