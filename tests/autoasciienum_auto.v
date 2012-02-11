// Code ok to distribute

module autoasciienum_auto();

   reg [2:0]   /* auto enum sm_psm */   sm_psm;
   reg [2:0]   /* auto enum sm_ps2 */   sm_ps2;

   localparam [2:0] // auto enum sm_psm
     PSM_IDL = 0,
     PSM_RST = 6,
     PSM_ZOT = 7;

   localparam [2:0] // auto enum sm_ps2
     PS2_IDL = 0,
     PS2_FOO = 1;

   /*AUTOASCIIENUM("sm_psm", "_sm_psm__ascii", "_")*/
   /*AUTOASCIIENUM("sm_ps2", "_sm_ps2__ascii", "_")*/

endmodule : autoasciienum_auto


