module sc_top (
               input var  real Tx_vcm,
               input var  real i_DAC_in,
               input      i_Tx_SC_en,
               output var real Tx_vsc
               );
   
endmodule


module cm_top (
               input      i_Tx_CM_en,
               output var real Tx_vcm
               );
   
endmodule

module top (
            /*AUTOOUTPUT*/
            // Beginning of automatic outputs (from unused autoinst outputs)
            output real Tx_vsc, // From sc_buf of sc_top.v
            // End of automatics
            /*AUTOINPUT*/
            // Beginning of automatic inputs (from unused autoinst inputs)
            input real  i_DAC_in, // To sc_buf of sc_top.v
            input       i_Tx_CM_en, // To cm_buf of cm_top.v
            input       i_Tx_SC_en              // To sc_buf of sc_top.v
            // End of automatics
            );
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   real Tx_vcm;                 // From cm_buf of cm_top.v
   // End of automatics
   
   cm_top cm_buf (/*AUTOINST*/
                  // Outputs
                  .Tx_vcm                       (Tx_vcm),
                  // Inputs
                  .i_Tx_CM_en           (i_Tx_CM_en));
   
   sc_top sc_buf (/*AUTOINST*/
                  // Outputs
                  .Tx_vsc                       (Tx_vsc),
                  // Inputs
                  .Tx_vcm                       (Tx_vcm),
                  .i_DAC_in             (i_DAC_in),
                  .i_Tx_SC_en           (i_Tx_SC_en));
   
endmodule
