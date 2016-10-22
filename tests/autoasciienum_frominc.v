module sm (/*AUTOARG*/);

   //==================== Constant declarations ==============

`include "autoasciienum_param.v"

   //==================== Intermediate Variables =============

   reg [3:0]	/* synopsys enum En_C14ChipNum */	chip_r;

   //==================== DEBUG ASCII CODE =========================

   /*AUTOASCIIENUM("chip_r", "chip_r__ascii","Ep_C14ChipNum_")*/
   // Beginning of automatic ASCII enum decoding
   reg [31:0]		chip_r__ascii;		// Decode of chip_r
   always @(chip_r) begin
      case ({chip_r})
	EP_C14ChipNum_RNP:  chip_r__ascii = "rnp ";
	EP_C14ChipNum_SPP:  chip_r__ascii = "spp ";
	EP_C14ChipNum_SRP:  chip_r__ascii = "srp ";
	EP_C14ChipNum_SMM2: chip_r__ascii = "smm2";
	EP_C14ChipNum_SMM:  chip_r__ascii = "smm ";
	EP_C14ChipNum_TTE:  chip_r__ascii = "tte ";
	EP_C14ChipNum_DLE:  chip_r__ascii = "dle ";
	EP_C14ChipNum_OASP: chip_r__ascii = "oasp";
	default:            chip_r__ascii = "%Err";
      endcase
   end
   // End of automatics

endmodule

//==== Emacs verilog-mode controls ====
// Local Variables:
// verilog-auto-read-includes:t
// End:
