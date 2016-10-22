// $Revision: #70 $$Date: 2002/10/19 $$Author: wsnyder $ -*- Verilog -*-
//====================================================================

module CmpEng (/*AUTOARG*/);

   input clk;
   input reset_l;

   // ****************************************************************

   /*AUTOREG*/
   /*AUTOWIRE*/

   // ********* Prefetch FSM definitions ****************************

   reg [3:0] m_cac_state_r;

   reg [2:0] m_cac_sel_r, m_dat_sel_r, m_cac_rw_sel_r;

   reg	     m_wid1_r;
   reg [2:0] m_wid3_r;
   reg [5:2] m_wid4_r_l;

   logic [4:1] logic_four;

   logic [PARAM-1:0] paramed;

`define M 2
`define L 1
   parameter MS = 2;
   parameter LS = 1;

   reg [MS:LS] m_param_r;
   reg [`M:`L] m_def2_r;

   always @ (posedge clk) begin
      if (~reset_l) begin
	 m_cac_state_r <= CAC_IDLE;
	 m_cac_sel_r <= CSEL_PF;
	 /*AUTORESET*/
      end
      else begin
	 m_wid1_r <= 0;
	 m_wid3_r <= 0;
	 m_wid4_r_l <= 0;
	 m_param_r <= 0;
	 m_def2_r <= 0;
	 logic_four <= 4;
	 paramed <= 1;
      end
   end

endmodule

// Local Variables:
// verilog-auto-read-includes:t
// verilog-auto-sense-defines-constant: t
// verilog-auto-reset-widths: t
// verilog-active-low-regexp: "_l$"
// End:
