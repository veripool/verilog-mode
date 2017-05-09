module x (/*AUTOARG*/);
   
   // Which Internal Bank
`define DMC_AG_HADDR_BADDR_BST2_RNG 1:0 // Bank Address Range within Hexabyte Address for 2-Burst
`define DMC_AG_HADDR_BADDR_BST4_RNG 2:1 // Bank Address Range within Hexabyte Address for 4-Burst
`define DMC_AG_HADDR_BADDR_BST8_RNG 3:2 // Bank Address Range within Hexabyte Address for 8-Burst
   
   reg [NumBnks-1:0]             ibnk_sel_s; // Muxed internal bank address subfield of
   command address
     always @(/*AUTOSENSE*/lio_buscfg_brstlen2_sr or lio_buscfg_brstlen4_sr or m_cdq_haddr_sr)
       begin : PeelIntBnkAddr
          case ({lio_buscfg_brstlen4_sr,lio_buscfg_brstlen2_sr})
            2'b01: // 2-burst
              begin
                 ibnk_sel_s = m_cdq_haddr_sr[`DMC_AG_HADDR_BADDR_BST2_RNG];
              end
            2'b10: // 4-burst
              begin
                 ibnk_sel_s = m_cdq_haddr_sr[`DMC_AG_HADDR_BADDR_BST4_RNG];
              end
            default: // 8-burst
              begin
                 ibnk_sel_s = m_cdq_haddr_sr[`DMC_AG_HADDR_BADDR_BST8_RNG];
              end
          endcase
       end
   
endmodule

// Local Variables:
// verilog-auto-read-includes:t
// End:
