module FswArbiter (/*AUTOARG*/) ;


   // ========================
   //  Include parameter File
   // ========================
  parameter DMAO = 0;

`include "chip_fsw_spec_param.v"

   // ===============
   //  Physical Pins
   // ===============

   input	  sclk;				// Fabric switch clock
   input	  lreset_l;

   input          csr_insert_idle;
   input          csr_arb_enable;

   input [3:0] 	  csr_bypass3_enable;
   input [3:0] 	  csr_bypass2_enable;
   input [3:0] 	  csr_bypass1_enable;

   input          csr_xb_ecc_enable;

   output [3:0]   xb_ecc_error_dbit;
   output [3:0]	  xb_ecc_error_1bit;

   output         insert_idle_ack;

   output [2:0]   bp_performance_count;

   input         xb0_obx_ReqPst_s2a;
   input [3:0] 	 xb0_obx_NextVc_s2a;
   input [1:0] 	 xb0_obx_NextPort_s2a;
   input [3:0] 	 xb0_obx_NextXbe_s2a;
   input [3:0] 	 xb0_obx_NextXbe_s3a;
   input [71:0]  xb0_obx_OutDat_s4a;

   output        obx_xb0_GntPst_s3a;
   output	 obx_xb0_GntByp_s3a;

   input         xb0_obx_ReqBypS3_s2a;
   input         xb0_obx_ReqBypS2_s2a;

   input         xb1_obx_ReqPst_s2a;
   input [3:0] 	 xb1_obx_NextVc_s2a;
   input [1:0] 	 xb1_obx_NextPort_s2a;
   input [3:0] 	 xb1_obx_NextXbe_s2a;
   input [3:0] 	 xb1_obx_NextXbe_s3a;
   input [71:0]  xb1_obx_OutDat_s4a;

   output        obx_xb1_GntPst_s3a;
   output	 obx_xb1_GntByp_s3a;

   input         xb1_obx_ReqBypS3_s2a;
   input         xb1_obx_ReqBypS2_s2a;

   input         xb2_obx_ReqPst_s2a;
   input [3:0] 	 xb2_obx_NextVc_s2a;
   input [1:0] 	 xb2_obx_NextPort_s2a;
   input [3:0] 	 xb2_obx_NextXbe_s2a;
   input [3:0] 	 xb2_obx_NextXbe_s3a;
   input [71:0]  xb2_obx_OutDat_s4a;

   output        obx_xb2_GntPst_s3a;
   output	 obx_xb2_GntByp_s3a;

   input         xb2_obx_ReqBypS3_s2a;
   input         xb2_obx_ReqBypS2_s2a;

   input         xb3_obx_ReqPst_s2a;
   input [3:0] 	 xb3_obx_NextVc_s2a;
   input [1:0] 	 xb3_obx_NextPort_s2a;
   input [3:0] 	 xb3_obx_NextXbe_s2a;
   input [3:0] 	 xb3_obx_NextXbe_s3a;
   input [71:0]  xb3_obx_OutDat_s4a;

   output        obx_xb3_GntPst_s3a;
   output	 obx_xb3_GntByp_s3a;

   input         xb3_obx_ReqBypS3_s2a;
   input         xb3_obx_ReqBypS2_s2a;

   input         ib0_obx_PortSel_s1a;
   input [63:0]  ib0_obx_InDat_s1a;
   input [1:0]	 ib0_obx_NextPort_s1a;
   input [3:0]   ib0_obx_NextVc_s1a;

   input         ib1_obx_PortSel_s1a;
   input [63:0]  ib1_obx_InDat_s1a;
   input [1:0]	 ib1_obx_NextPort_s1a;
   input [3:0]   ib1_obx_NextVc_s1a;

   input         ib2_obx_PortSel_s1a;
   input [63:0]  ib2_obx_InDat_s1a;
   input [1:0]	 ib2_obx_NextPort_s1a;
   input [3:0]   ib2_obx_NextVc_s1a;

   input         ib3_obx_PortSel_s1a;
   input [63:0]  ib3_obx_InDat_s1a;
   input [1:0]	 ib3_obx_NextPort_s1a;
   input [3:0]   ib3_obx_NextVc_s1a;

   input         rp_is_full;
   input         rp_in_progress;

   input [15:0]  rp_arb_poolmask;
   input [63:0]  rp_arb_bufbusy_mask;

   output        xbx_grant_cycle;
   output        bp1_grant_cycle;
   output        set_arbitration_enable_d1;

   output [63:0] reset_ackbuf;
   output [63:0] wait_for_ack;

   output [63:0] ice9_databus;

   // =============================
   // Auto Wires/Regs
   // =============================

   /*AUTOWIRE*/
   /*AUTOREG*/

/* FswBypassArbiter AUTO_TEMPLATE (
			   // Outputs
			   .bp_grant3			(bp@_grant3),
			   .bp_grant2			(bp@_grant2),
			   .bp_grant1			(bp@_grant1),
			   .bp_grant0			(bp@_grant0),
			   .bp_grant_cycle		(bp@_grant_cycle),
			   .bp_grant_cycle_d1		(bp@_grant_cycle_d1),
			   .bp_grant_cycle_d2		(bp@_grant_cycle_d2),
			   .bp_next_winner		(bp@_next_winner[1:0]),
			   .bp_next_winner_d1		(bp@_next_winner_d1[1:0]),
			   .bp_next_winner_d2		(bp@_next_winner_d2[1:0]),
			   .bp_nextxbe			(bp@_nextxbe[3:0]),
			   .bp_nextxbe_d1		(bp@_nextxbe_d1[3:0]),
			   .bp_nextxbe_d2		(bp@_nextxbe_d2[3:0]),
			   .bp_hold_wait_vector		(bp@_hold_wait_vector[5:0]),
			   .bp_hold_wait_vector_d1	(bp@_hold_wait_vector_d1[5:0]),
			   .bp_select			(bp@_select),
			   .bp_select_d1		(bp@_select_d1),
			   .bp_select_d2		(bp@_select_d2),
			   .bp_header			(bp@_header),
			   .bp_header_d1		(bp@_header_d1),
			   .bp_header_d2		(bp@_header_d2),
			   // Inputs
			   .lreset_l			(bp@_lreset_l),
			   .bp_arb_enable		(bp@_arb_enable),
			   .sop3			(sop3 & xbx_bp3_enable_3),
			   .sop2			(sop2 & xbx_bp3_enable_2),
			   .sop1			(sop1 & xbx_bp3_enable_1),
			   .sop0			(sop0 & xbx_bp3_enable_0),
			   ); */


   FswBypassArbiter bp3 (/*AUTOINST*/);


/* FswBypassArbiter AUTO_TEMPLATE (
			   // Outputs
			   .bp_grant3			(bp@_grant3),
			   .bp_grant2			(bp@_grant2),
			   .bp_grant1			(bp@_grant1),
			   .bp_grant0			(bp@_grant0),
			   .bp_grant_cycle		(bp@_grant_cycle),
			   .bp_grant_cycle_d1		(bp@_grant_cycle_d1),
			   .bp_grant_cycle_d2		(bp@_grant_cycle_d2),
			   .bp_next_winner		(bp@_next_winner[1:0]),
			   .bp_next_winner_d1		(bp@_next_winner_d1[1:0]),
			   .bp_next_winner_d2		(bp@_next_winner_d2[1:0]),
			   .bp_nextxbe			(bp@_nextxbe[3:0]),
			   .bp_nextxbe_d1		(bp@_nextxbe_d1[3:0]),
			   .bp_nextxbe_d2		(bp@_nextxbe_d2[3:0]),
			   .bp_hold_wait_vector		(bp@_hold_wait_vector[5:0]),
			   .bp_hold_wait_vector_d1	(bp@_hold_wait_vector_d1[5:0]),
			   .bp_select			(bp@_select),
			   .bp_select_d1		(bp@_select_d1),
			   .bp_select_d2		(bp@_select_d2),
			   .bp_header			(bp@_header),
			   .bp_header_d1		(bp@_header_d1),
			   .bp_header_d2		(bp@_header_d2),
			   // Inputs
			   .lreset_l			(bp@_lreset_l),
			   .bp_arb_enable		(bp@_arb_enable),
			   .sop3			(sop3 & xbx_bp2_enable_3),
			   .sop2			(sop2 & xbx_bp2_enable_2),
			   .sop1			(sop1 & xbx_bp2_enable_1),
			   .sop0			(sop0 & xbx_bp2_enable_0),
			   ); */


   FswBypassArbiter bp2 (/*AUTOINST*/);


/* FswBypassArbiter AUTO_TEMPLATE (
			   // Outputs
			   .bp_grant3			(bp@_grant3),
			   .bp_grant2			(bp@_grant2),
			   .bp_grant1			(bp@_grant1),
			   .bp_grant0			(bp@_grant0),
			   .bp_grant_cycle		(bp@_grant_cycle),
			   .bp_grant_cycle_d1		(bp@_grant_cycle_d1),
			   .bp_grant_cycle_d2		(bp@_grant_cycle_d2),
			   .bp_next_winner		(bp@_next_winner[1:0]),
			   .bp_next_winner_d1		(bp@_next_winner_d1[1:0]),
			   .bp_next_winner_d2		(bp@_next_winner_d2[1:0]),
			   .bp_nextxbe			(bp@_nextxbe[3:0]),
			   .bp_nextxbe_d1		(bp@_nextxbe_d1[3:0]),
			   .bp_nextxbe_d2		(bp@_nextxbe_d2[3:0]),
			   .bp_hold_wait_vector		(bp@_hold_wait_vector[5:0]),
			   .bp_hold_wait_vector_d1	(bp@_hold_wait_vector_d1[5:0]),
			   .bp_select			(bp@_select),
			   .bp_select_d1		(bp@_select_d1),
			   .bp_select_d2		(bp@_select_d2),
			   .bp_header			(bp@_header),
			   .bp_header_d1		(bp@_header_d1),
			   .bp_header_d2		(bp@_header_d2),
			   // Inputs
			   .lreset_l			(bp@_lreset_l),
			   .bp_arb_enable		(bp@_arb_enable),
			   .sop3			(sop3 & csr_bp1_enable_3),
			   .sop2			(sop2 & csr_bp1_enable_2),
			   .sop1			(sop1 & csr_bp1_enable_1),
			   .sop0			(sop0 & csr_bp1_enable_0),
			   ); */


   FswBypassArbiter bp1 (/*AUTOINST*/);


   // =======================================
   // Coverage
   // =======================================

   // psl default clock = negedge sclk;
   generate if (DMAO == 0)
     begin
   // psl cover {lreset_l & (bp1_grant0 |bp1_grant1 |bp1_grant2 |bp1_grant3 )} report "FswPerfRtl::byp1Taken";
   // psl cover {lreset_l & (bp2_grant0 |bp2_grant1 |bp2_grant2 |bp2_grant3)} report "FswPerfRtl::byp2Taken";
   // psl cover {lreset_l & (bp3_grant0 |bp3_grant1 |bp3_grant2 |bp3_grant3)} report "FswPerfRtl::byp3Taken";
     end
   endgenerate

   // ================
   //  Unused signals
   // ================

   // lint_checking SCX_UNUSED off
   wire _unused_ok = &{1'b0,

		       bp_select,

		       bp3_hold_wait_vector,
		       bp2_hold_wait_vector_d1,
		       bp1_hold_wait_vector_d1,

		       bp3_header,
		       bp3_header_d1,
		       bp3_select,
		       bp3_select_d1,
		       bp3_next_winner[1:0],
		       bp3_next_winner_d1[1:0],
		       bp3_nextxbe[3:0],
		       bp3_nextxbe_d1[3:0],


		       bp2_grant_cycle_d2,
		       bp2_header,
		       bp2_header_d2,
		       bp2_select,
		       bp2_select_d2,
		       bp2_next_winner[1:0],
		       bp2_next_winner_d2[1:0],
		       bp2_nextxbe[3:0],
		       bp2_nextxbe_d2[3:0],

		       bp1_header_d1,
		       bp1_header_d2,
		       bp1_select_d1,
		       bp1_select_d2,
		       bp1_next_winner_d1[1:0],
		       bp1_next_winner_d2[1:0],
		       bp1_nextxbe_d1[3:0],
		       bp1_nextxbe_d2[3:0],

		       xb0_obx_NextXbe_s3a,	// This is unused signal now.
		       xb1_obx_NextXbe_s3a,
		       xb2_obx_NextXbe_s3a,
		       xb3_obx_NextXbe_s3a,

		       syn64,
		       dataout64,

		       1'b0
		       };
   // lint_checking SCX_UNUSED on


endmodule

module FswBypassArbiter (/*AUTOARG*/) ;

   input        lreset_l;
   input	sclk;
   input	bp_arb_enable;
   output       bp_grant3;
   output       bp_grant2;
   output       bp_grant1;
   output       bp_grant0;
   output  	bp_grant_cycle;
   output 	bp_grant_cycle_d1;
   output 	bp_grant_cycle_d2;
   output [1:0] bp_next_winner;
   output [1:0]	bp_next_winner_d1;
   output [1:0]	bp_next_winner_d2;
   output [3:0] bp_nextxbe;
   output [3:0] bp_nextxbe_d1;
   output [3:0] bp_nextxbe_d2;
   output [5:0]	bp_hold_wait_vector;
   output [5:0]	bp_hold_wait_vector_d1;
   output	bp_header;
   output	bp_header_d1;
   output	bp_header_d2;
   output	bp_select;
   output	bp_select_d1;
   output	bp_select_d2;
   input 	sop3;
   input [63:0] sop3_data;
   input [5:0]  sop3_bpcontext;
   input 	sop2;
   input [63:0] sop2_data;
   input [5:0]  sop2_bpcontext;
   input 	sop1;
   input [63:0] sop1_data;
   input [5:0]  sop1_bpcontext;
   input 	sop0;
   input [63:0] sop0_data;
   input [5:0]  sop0_bpcontext;
   input [15:0] poolmask;
   input [63:0] bufbusy_mask;
endmodule
