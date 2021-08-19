// Code ok to distribute

module autoasciienum_auto();
   
   reg [2:0]        /* auto enum sm_psm */ sm_psm;
   reg [2:0]        /* auto enum sm_ps2 */ sm_ps2;
   
   localparam [2:0] // auto enum sm_psm
                    PSM_IDL = 0,
                    PSM_RST = 6,
                    PSM_ZOT = 7;
   
   localparam [2:0] // auto enum sm_ps2
                    PS2_IDL = 0,
                    PS2_FOO = 1;
   
   /*AUTOASCIIENUM("sm_psm", "_sm_psm__ascii", "_")*/
   // Beginning of automatic ASCII enum decoding
   reg [47:0]       _sm_psm__ascii;             // Decode of sm_psm
   always @(sm_psm) begin
      case ({sm_psm})
        PSM_IDL:  _sm_psm__ascii = "psmidl";
        PSM_RST:  _sm_psm__ascii = "psmrst";
        PSM_ZOT:  _sm_psm__ascii = "psmzot";
        default:  _sm_psm__ascii = "%Error";
      endcase
   end
   // End of automatics
   /*AUTOASCIIENUM("sm_ps2", "_sm_ps2__ascii", "_")*/
   // Beginning of automatic ASCII enum decoding
   reg [47:0] _sm_ps2__ascii;           // Decode of sm_ps2
   always @(sm_ps2) begin
      case ({sm_ps2})
        PS2_IDL:  _sm_ps2__ascii = "ps2idl";
        PS2_FOO:  _sm_ps2__ascii = "ps2foo";
        default:  _sm_ps2__ascii = "%Error";
      endcase
   end
   // End of automatics
   
endmodule : autoasciienum_auto


