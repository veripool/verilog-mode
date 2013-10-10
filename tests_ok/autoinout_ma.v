module foo
  (
   input  soutb,
   output sina,
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input  sinb, // To i_bar of bar.v
   // End of automatics
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output souta                 // From i_bar of bar.v
   // End of automatics
   ) ;
   bar i_bar(/*AUTOINST*/
             // Outputs
             .souta                     (souta),
             .soutb                     (soutb),
             // Inputs
             .sina                      (sina),
             .sinb                      (sinb));
   
endmodule // foo

module bar (/*AUTOARG*/
            // Outputs
            souta, soutb,
            // Inputs
            sina, sinb
            ) ;
   input  sina, sinb;
   output souta, soutb;
endmodule // bar
