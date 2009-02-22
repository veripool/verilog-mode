module io1_sub(
               /*AUTOARG*/
               // Outputs
               lower_out,
               // Inputs
               lower_ina
               );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input  lower_ina; // To inst of inst.v
   // End of automatics
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output lower_out;            // From inst of inst.v
   // End of automatics
   
   /* inst AUTO_TEMPLATE (
    .lower_inb          (1'b1),
    )*/
   
   
   inst inst (/*AUTOINST*/
              // Outputs
              .lower_out                (lower_out),
              // Inputs
              .lower_inb                (1'b1),                  // Templated
              .lower_ina                (lower_ina));
   
endmodule
