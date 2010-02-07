
// 2001 Parameter Style
module v2k_inst_hicks (
                       output wire [7:0] relay,
                       output wire       relay_f,
                       output wire       swen_f0_n,
                       input [31:0]      dcb,
                       input             relay_ce,
                       input wire        simReset,
                       input wire        clock
                       );
   
   input [31:0] dcb_n2k;
   
   // AUTOINST results  NOT OK
   v2k_inst_hicks v2k_inst_hicks (/*AUTOINST*/
                                  // Outputs
                                  .relay                (relay[7:0]),
                                  .relay_f              (relay_f),
                                  .swen_f0_n            (swen_f0_n),
                                  // Inputs
                                  .dcb                  (dcb[31:0]),
                                  .relay_ce             (relay_ce),
                                  .simReset             (simReset),
                                  .clock                (clock),
                                  .dcb_n2k              (dcb_n2k[31:0]));
   
endmodule
