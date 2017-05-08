module FswArbiter (/*AUTOARG*/
                   // Outputs
                   xb_ecc_error_dbit, xb_ecc_error_1bit, insert_idle_ack, bp_performance_count, obx_xb0_GntPst_s3a,
                   obx_xb0_GntByp_s3a, obx_xb1_GntPst_s3a, obx_xb1_GntByp_s3a, obx_xb2_GntPst_s3a,
                   obx_xb2_GntByp_s3a, obx_xb3_GntPst_s3a, obx_xb3_GntByp_s3a, xbx_grant_cycle, bp1_grant_cycle,
                   set_arbitration_enable_d1, reset_ackbuf, wait_for_ack, ice9_databus,
                   // Inputs
                   sclk, lreset_l, csr_insert_idle, csr_arb_enable, csr_bypass3_enable, csr_bypass2_enable,
                   csr_bypass1_enable, csr_xb_ecc_enable, xb0_obx_ReqPst_s2a, xb0_obx_NextVc_s2a,
                   xb0_obx_NextPort_s2a, xb0_obx_NextXbe_s2a, xb0_obx_NextXbe_s3a, xb0_obx_OutDat_s4a,
                   xb0_obx_ReqBypS3_s2a, xb0_obx_ReqBypS2_s2a, xb1_obx_ReqPst_s2a, xb1_obx_NextVc_s2a,
                   xb1_obx_NextPort_s2a, xb1_obx_NextXbe_s2a, xb1_obx_NextXbe_s3a, xb1_obx_OutDat_s4a,
                   xb1_obx_ReqBypS3_s2a, xb1_obx_ReqBypS2_s2a, xb2_obx_ReqPst_s2a, xb2_obx_NextVc_s2a,
                   xb2_obx_NextPort_s2a, xb2_obx_NextXbe_s2a, xb2_obx_NextXbe_s3a, xb2_obx_OutDat_s4a,
                   xb2_obx_ReqBypS3_s2a, xb2_obx_ReqBypS2_s2a, xb3_obx_ReqPst_s2a, xb3_obx_NextVc_s2a,
                   xb3_obx_NextPort_s2a, xb3_obx_NextXbe_s2a, xb3_obx_NextXbe_s3a, xb3_obx_OutDat_s4a,
                   xb3_obx_ReqBypS3_s2a, xb3_obx_ReqBypS2_s2a, ib0_obx_PortSel_s1a, ib0_obx_InDat_s1a,
                   ib0_obx_NextPort_s1a, ib0_obx_NextVc_s1a, ib1_obx_PortSel_s1a, ib1_obx_InDat_s1a,
                   ib1_obx_NextPort_s1a, ib1_obx_NextVc_s1a, ib2_obx_PortSel_s1a, ib2_obx_InDat_s1a,
                   ib2_obx_NextPort_s1a, ib2_obx_NextVc_s1a, ib3_obx_PortSel_s1a, ib3_obx_InDat_s1a,
                   ib3_obx_NextPort_s1a, ib3_obx_NextVc_s1a, rp_is_full, rp_in_progress, rp_arb_poolmask,
                   rp_arb_bufbusy_mask
                   ) ;
   
   
   // ========================
   //  Include parameter File
   // ========================
   parameter DMAO = 0;
   
`include "chip_fsw_spec_param.v"
   
   // ===============
   //  Physical Pins
   // ===============
   
   input         sclk; // Fabric switch clock
   input         lreset_l;
   
   input         csr_insert_idle;
   input         csr_arb_enable;
   
   input [3:0]   csr_bypass3_enable;
   input [3:0]   csr_bypass2_enable;
   input [3:0]   csr_bypass1_enable;
   
   input         csr_xb_ecc_enable;
   
   output [3:0]  xb_ecc_error_dbit;
   output [3:0]  xb_ecc_error_1bit;
   
   output        insert_idle_ack;
   
   output [2:0]  bp_performance_count;
   
   input         xb0_obx_ReqPst_s2a;
   input [3:0]   xb0_obx_NextVc_s2a;
   input [1:0]   xb0_obx_NextPort_s2a;
   input [3:0]   xb0_obx_NextXbe_s2a;
   input [3:0]   xb0_obx_NextXbe_s3a;
   input [71:0]  xb0_obx_OutDat_s4a;
   
   output        obx_xb0_GntPst_s3a;
   output        obx_xb0_GntByp_s3a;
   
   input         xb0_obx_ReqBypS3_s2a;
   input         xb0_obx_ReqBypS2_s2a;
   
   input         xb1_obx_ReqPst_s2a;
   input [3:0]   xb1_obx_NextVc_s2a;
   input [1:0]   xb1_obx_NextPort_s2a;
   input [3:0]   xb1_obx_NextXbe_s2a;
   input [3:0]   xb1_obx_NextXbe_s3a;
   input [71:0]  xb1_obx_OutDat_s4a;
   
   output        obx_xb1_GntPst_s3a;
   output        obx_xb1_GntByp_s3a;
   
   input         xb1_obx_ReqBypS3_s2a;
   input         xb1_obx_ReqBypS2_s2a;
   
   input         xb2_obx_ReqPst_s2a;
   input [3:0]   xb2_obx_NextVc_s2a;
   input [1:0]   xb2_obx_NextPort_s2a;
   input [3:0]   xb2_obx_NextXbe_s2a;
   input [3:0]   xb2_obx_NextXbe_s3a;
   input [71:0]  xb2_obx_OutDat_s4a;
   
   output        obx_xb2_GntPst_s3a;
   output        obx_xb2_GntByp_s3a;
   
   input         xb2_obx_ReqBypS3_s2a;
   input         xb2_obx_ReqBypS2_s2a;
   
   input         xb3_obx_ReqPst_s2a;
   input [3:0]   xb3_obx_NextVc_s2a;
   input [1:0]   xb3_obx_NextPort_s2a;
   input [3:0]   xb3_obx_NextXbe_s2a;
   input [3:0]   xb3_obx_NextXbe_s3a;
   input [71:0]  xb3_obx_OutDat_s4a;
   
   output        obx_xb3_GntPst_s3a;
   output        obx_xb3_GntByp_s3a;
   
   input         xb3_obx_ReqBypS3_s2a;
   input         xb3_obx_ReqBypS2_s2a;
   
   input         ib0_obx_PortSel_s1a;
   input [63:0]  ib0_obx_InDat_s1a;
   input [1:0]   ib0_obx_NextPort_s1a;
   input [3:0]   ib0_obx_NextVc_s1a;
   
   input         ib1_obx_PortSel_s1a;
   input [63:0]  ib1_obx_InDat_s1a;
   input [1:0]   ib1_obx_NextPort_s1a;
   input [3:0]   ib1_obx_NextVc_s1a;
   
   input         ib2_obx_PortSel_s1a;
   input [63:0]  ib2_obx_InDat_s1a;
   input [1:0]   ib2_obx_NextPort_s1a;
   input [3:0]   ib2_obx_NextVc_s1a;
   
   input         ib3_obx_PortSel_s1a;
   input [63:0]  ib3_obx_InDat_s1a;
   input [1:0]   ib3_obx_NextPort_s1a;
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
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire          bp1_grant0; // From bp1 of FswBypassArbiter.v
   wire          bp1_grant1; // From bp1 of FswBypassArbiter.v
   wire          bp1_grant2; // From bp1 of FswBypassArbiter.v
   wire          bp1_grant3; // From bp1 of FswBypassArbiter.v
   wire          bp1_grant_cycle_d1; // From bp1 of FswBypassArbiter.v
   wire          bp1_grant_cycle_d2; // From bp1 of FswBypassArbiter.v
   wire          bp1_header; // From bp1 of FswBypassArbiter.v
   wire          bp1_header_d1; // From bp1 of FswBypassArbiter.v
   wire          bp1_header_d2; // From bp1 of FswBypassArbiter.v
   wire [5:0]    bp1_hold_wait_vector; // From bp1 of FswBypassArbiter.v
   wire [5:0]    bp1_hold_wait_vector_d1;// From bp1 of FswBypassArbiter.v
   wire [1:0]    bp1_next_winner; // From bp1 of FswBypassArbiter.v
   wire [1:0]    bp1_next_winner_d1; // From bp1 of FswBypassArbiter.v
   wire [1:0]    bp1_next_winner_d2; // From bp1 of FswBypassArbiter.v
   wire [3:0]    bp1_nextxbe; // From bp1 of FswBypassArbiter.v
   wire [3:0]    bp1_nextxbe_d1; // From bp1 of FswBypassArbiter.v
   wire [3:0]    bp1_nextxbe_d2; // From bp1 of FswBypassArbiter.v
   wire          bp1_select; // From bp1 of FswBypassArbiter.v
   wire          bp1_select_d1; // From bp1 of FswBypassArbiter.v
   wire          bp1_select_d2; // From bp1 of FswBypassArbiter.v
   wire          bp2_grant0; // From bp2 of FswBypassArbiter.v
   wire          bp2_grant1; // From bp2 of FswBypassArbiter.v
   wire          bp2_grant2; // From bp2 of FswBypassArbiter.v
   wire          bp2_grant3; // From bp2 of FswBypassArbiter.v
   wire          bp2_grant_cycle; // From bp2 of FswBypassArbiter.v
   wire          bp2_grant_cycle_d1; // From bp2 of FswBypassArbiter.v
   wire          bp2_grant_cycle_d2; // From bp2 of FswBypassArbiter.v
   wire          bp2_header; // From bp2 of FswBypassArbiter.v
   wire          bp2_header_d1; // From bp2 of FswBypassArbiter.v
   wire          bp2_header_d2; // From bp2 of FswBypassArbiter.v
   wire [5:0]    bp2_hold_wait_vector; // From bp2 of FswBypassArbiter.v
   wire [5:0]    bp2_hold_wait_vector_d1;// From bp2 of FswBypassArbiter.v
   wire [1:0]    bp2_next_winner; // From bp2 of FswBypassArbiter.v
   wire [1:0]    bp2_next_winner_d1; // From bp2 of FswBypassArbiter.v
   wire [1:0]    bp2_next_winner_d2; // From bp2 of FswBypassArbiter.v
   wire [3:0]    bp2_nextxbe; // From bp2 of FswBypassArbiter.v
   wire [3:0]    bp2_nextxbe_d1; // From bp2 of FswBypassArbiter.v
   wire [3:0]    bp2_nextxbe_d2; // From bp2 of FswBypassArbiter.v
   wire          bp2_select; // From bp2 of FswBypassArbiter.v
   wire          bp2_select_d1; // From bp2 of FswBypassArbiter.v
   wire          bp2_select_d2; // From bp2 of FswBypassArbiter.v
   wire          bp3_grant0; // From bp3 of FswBypassArbiter.v
   wire          bp3_grant1; // From bp3 of FswBypassArbiter.v
   wire          bp3_grant2; // From bp3 of FswBypassArbiter.v
   wire          bp3_grant3; // From bp3 of FswBypassArbiter.v
   wire          bp3_grant_cycle; // From bp3 of FswBypassArbiter.v
   wire          bp3_grant_cycle_d1; // From bp3 of FswBypassArbiter.v
   wire          bp3_grant_cycle_d2; // From bp3 of FswBypassArbiter.v
   wire          bp3_header; // From bp3 of FswBypassArbiter.v
   wire          bp3_header_d1; // From bp3 of FswBypassArbiter.v
   wire          bp3_header_d2; // From bp3 of FswBypassArbiter.v
   wire [5:0]    bp3_hold_wait_vector; // From bp3 of FswBypassArbiter.v
   wire [5:0]    bp3_hold_wait_vector_d1;// From bp3 of FswBypassArbiter.v
   wire [1:0]    bp3_next_winner; // From bp3 of FswBypassArbiter.v
   wire [1:0]    bp3_next_winner_d1; // From bp3 of FswBypassArbiter.v
   wire [1:0]    bp3_next_winner_d2; // From bp3 of FswBypassArbiter.v
   wire [3:0]    bp3_nextxbe; // From bp3 of FswBypassArbiter.v
   wire [3:0]    bp3_nextxbe_d1; // From bp3 of FswBypassArbiter.v
   wire [3:0]    bp3_nextxbe_d2; // From bp3 of FswBypassArbiter.v
   wire          bp3_select; // From bp3 of FswBypassArbiter.v
   wire          bp3_select_d1; // From bp3 of FswBypassArbiter.v
   wire          bp3_select_d2; // From bp3 of FswBypassArbiter.v
   // End of automatics
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [2:0]     bp_performance_count;
   reg [63:0]    ice9_databus;
   reg           insert_idle_ack;
   reg           obx_xb0_GntByp_s3a;
   reg           obx_xb0_GntPst_s3a;
   reg           obx_xb1_GntByp_s3a;
   reg           obx_xb1_GntPst_s3a;
   reg           obx_xb2_GntByp_s3a;
   reg           obx_xb2_GntPst_s3a;
   reg           obx_xb3_GntByp_s3a;
   reg           obx_xb3_GntPst_s3a;
   reg [63:0]    reset_ackbuf;
   reg           set_arbitration_enable_d1;
   reg [63:0]    wait_for_ack;
   reg [3:0]     xb_ecc_error_1bit;
   reg [3:0]     xb_ecc_error_dbit;
   reg           xbx_grant_cycle;
   // End of automatics
   
   /* FswBypassArbiter AUTO_TEMPLATE (
    // Outputs
    .bp_grant3                  (bp@_grant3),
    .bp_grant2                  (bp@_grant2),
    .bp_grant1                  (bp@_grant1),
    .bp_grant0                  (bp@_grant0),
    .bp_grant_cycle             (bp@_grant_cycle),
    .bp_grant_cycle_d1          (bp@_grant_cycle_d1),
    .bp_grant_cycle_d2          (bp@_grant_cycle_d2),
    .bp_next_winner             (bp@_next_winner[1:0]),
    .bp_next_winner_d1          (bp@_next_winner_d1[1:0]),
    .bp_next_winner_d2          (bp@_next_winner_d2[1:0]),
    .bp_nextxbe                 (bp@_nextxbe[3:0]),
    .bp_nextxbe_d1              (bp@_nextxbe_d1[3:0]),
    .bp_nextxbe_d2              (bp@_nextxbe_d2[3:0]),
    .bp_hold_wait_vector                (bp@_hold_wait_vector[5:0]),
    .bp_hold_wait_vector_d1     (bp@_hold_wait_vector_d1[5:0]),
    .bp_select                  (bp@_select),
    .bp_select_d1               (bp@_select_d1),
    .bp_select_d2               (bp@_select_d2),
    .bp_header                  (bp@_header),
    .bp_header_d1               (bp@_header_d1),
    .bp_header_d2               (bp@_header_d2),
    // Inputs
    .lreset_l                   (bp@_lreset_l),
    .bp_arb_enable              (bp@_arb_enable),
    .sop3                       (sop3 & xbx_bp3_enable_3),
    .sop2                       (sop2 & xbx_bp3_enable_2),
    .sop1                       (sop1 & xbx_bp3_enable_1),
    .sop0                       (sop0 & xbx_bp3_enable_0),
    ); */
   
   
   FswBypassArbiter bp3 (/*AUTOINST*/
                         // Outputs
                         .bp_grant3             (bp3_grant3),    // Templated
                         .bp_grant2             (bp3_grant2),    // Templated
                         .bp_grant1             (bp3_grant1),    // Templated
                         .bp_grant0             (bp3_grant0),    // Templated
                         .bp_grant_cycle        (bp3_grant_cycle), // Templated
                         .bp_grant_cycle_d1     (bp3_grant_cycle_d1), // Templated
                         .bp_grant_cycle_d2     (bp3_grant_cycle_d2), // Templated
                         .bp_next_winner        (bp3_next_winner[1:0]), // Templated
                         .bp_next_winner_d1     (bp3_next_winner_d1[1:0]), // Templated
                         .bp_next_winner_d2     (bp3_next_winner_d2[1:0]), // Templated
                         .bp_nextxbe            (bp3_nextxbe[3:0]), // Templated
                         .bp_nextxbe_d1         (bp3_nextxbe_d1[3:0]), // Templated
                         .bp_nextxbe_d2         (bp3_nextxbe_d2[3:0]), // Templated
                         .bp_hold_wait_vector   (bp3_hold_wait_vector[5:0]), // Templated
                         .bp_hold_wait_vector_d1(bp3_hold_wait_vector_d1[5:0]), // Templated
                         .bp_header             (bp3_header),    // Templated
                         .bp_header_d1          (bp3_header_d1), // Templated
                         .bp_header_d2          (bp3_header_d2), // Templated
                         .bp_select             (bp3_select),    // Templated
                         .bp_select_d1          (bp3_select_d1), // Templated
                         .bp_select_d2          (bp3_select_d2), // Templated
                         // Inputs
                         .lreset_l              (bp3_lreset_l),  // Templated
                         .sclk                  (sclk),
                         .bp_arb_enable         (bp3_arb_enable), // Templated
                         .sop3                  (sop3 & xbx_bp3_enable_3), // Templated
                         .sop3_data             (sop3_data[63:0]),
                         .sop3_bpcontext        (sop3_bpcontext[5:0]),
                         .sop2                  (sop2 & xbx_bp3_enable_2), // Templated
                         .sop2_data             (sop2_data[63:0]),
                         .sop2_bpcontext        (sop2_bpcontext[5:0]),
                         .sop1                  (sop1 & xbx_bp3_enable_1), // Templated
                         .sop1_data             (sop1_data[63:0]),
                         .sop1_bpcontext        (sop1_bpcontext[5:0]),
                         .sop0                  (sop0 & xbx_bp3_enable_0), // Templated
                         .sop0_data             (sop0_data[63:0]),
                         .sop0_bpcontext        (sop0_bpcontext[5:0]),
                         .poolmask              (poolmask[15:0]),
                         .bufbusy_mask          (bufbusy_mask[63:0]));
   
   
   /* FswBypassArbiter AUTO_TEMPLATE (
    // Outputs
    .bp_grant3                  (bp@_grant3),
    .bp_grant2                  (bp@_grant2),
    .bp_grant1                  (bp@_grant1),
    .bp_grant0                  (bp@_grant0),
    .bp_grant_cycle             (bp@_grant_cycle),
    .bp_grant_cycle_d1          (bp@_grant_cycle_d1),
    .bp_grant_cycle_d2          (bp@_grant_cycle_d2),
    .bp_next_winner             (bp@_next_winner[1:0]),
    .bp_next_winner_d1          (bp@_next_winner_d1[1:0]),
    .bp_next_winner_d2          (bp@_next_winner_d2[1:0]),
    .bp_nextxbe                 (bp@_nextxbe[3:0]),
    .bp_nextxbe_d1              (bp@_nextxbe_d1[3:0]),
    .bp_nextxbe_d2              (bp@_nextxbe_d2[3:0]),
    .bp_hold_wait_vector                (bp@_hold_wait_vector[5:0]),
    .bp_hold_wait_vector_d1     (bp@_hold_wait_vector_d1[5:0]),
    .bp_select                  (bp@_select),
    .bp_select_d1               (bp@_select_d1),
    .bp_select_d2               (bp@_select_d2),
    .bp_header                  (bp@_header),
    .bp_header_d1               (bp@_header_d1),
    .bp_header_d2               (bp@_header_d2),
    // Inputs
    .lreset_l                   (bp@_lreset_l),
    .bp_arb_enable              (bp@_arb_enable),
    .sop3                       (sop3 & xbx_bp2_enable_3),
    .sop2                       (sop2 & xbx_bp2_enable_2),
    .sop1                       (sop1 & xbx_bp2_enable_1),
    .sop0                       (sop0 & xbx_bp2_enable_0),
    ); */
   
   
   FswBypassArbiter bp2 (/*AUTOINST*/
                         // Outputs
                         .bp_grant3             (bp2_grant3),    // Templated
                         .bp_grant2             (bp2_grant2),    // Templated
                         .bp_grant1             (bp2_grant1),    // Templated
                         .bp_grant0             (bp2_grant0),    // Templated
                         .bp_grant_cycle        (bp2_grant_cycle), // Templated
                         .bp_grant_cycle_d1     (bp2_grant_cycle_d1), // Templated
                         .bp_grant_cycle_d2     (bp2_grant_cycle_d2), // Templated
                         .bp_next_winner        (bp2_next_winner[1:0]), // Templated
                         .bp_next_winner_d1     (bp2_next_winner_d1[1:0]), // Templated
                         .bp_next_winner_d2     (bp2_next_winner_d2[1:0]), // Templated
                         .bp_nextxbe            (bp2_nextxbe[3:0]), // Templated
                         .bp_nextxbe_d1         (bp2_nextxbe_d1[3:0]), // Templated
                         .bp_nextxbe_d2         (bp2_nextxbe_d2[3:0]), // Templated
                         .bp_hold_wait_vector   (bp2_hold_wait_vector[5:0]), // Templated
                         .bp_hold_wait_vector_d1(bp2_hold_wait_vector_d1[5:0]), // Templated
                         .bp_header             (bp2_header),    // Templated
                         .bp_header_d1          (bp2_header_d1), // Templated
                         .bp_header_d2          (bp2_header_d2), // Templated
                         .bp_select             (bp2_select),    // Templated
                         .bp_select_d1          (bp2_select_d1), // Templated
                         .bp_select_d2          (bp2_select_d2), // Templated
                         // Inputs
                         .lreset_l              (bp2_lreset_l),  // Templated
                         .sclk                  (sclk),
                         .bp_arb_enable         (bp2_arb_enable), // Templated
                         .sop3                  (sop3 & xbx_bp2_enable_3), // Templated
                         .sop3_data             (sop3_data[63:0]),
                         .sop3_bpcontext        (sop3_bpcontext[5:0]),
                         .sop2                  (sop2 & xbx_bp2_enable_2), // Templated
                         .sop2_data             (sop2_data[63:0]),
                         .sop2_bpcontext        (sop2_bpcontext[5:0]),
                         .sop1                  (sop1 & xbx_bp2_enable_1), // Templated
                         .sop1_data             (sop1_data[63:0]),
                         .sop1_bpcontext        (sop1_bpcontext[5:0]),
                         .sop0                  (sop0 & xbx_bp2_enable_0), // Templated
                         .sop0_data             (sop0_data[63:0]),
                         .sop0_bpcontext        (sop0_bpcontext[5:0]),
                         .poolmask              (poolmask[15:0]),
                         .bufbusy_mask          (bufbusy_mask[63:0]));
   
   
   /* FswBypassArbiter AUTO_TEMPLATE (
    // Outputs
    .bp_grant3                  (bp@_grant3),
    .bp_grant2                  (bp@_grant2),
    .bp_grant1                  (bp@_grant1),
    .bp_grant0                  (bp@_grant0),
    .bp_grant_cycle             (bp@_grant_cycle),
    .bp_grant_cycle_d1          (bp@_grant_cycle_d1),
    .bp_grant_cycle_d2          (bp@_grant_cycle_d2),
    .bp_next_winner             (bp@_next_winner[1:0]),
    .bp_next_winner_d1          (bp@_next_winner_d1[1:0]),
    .bp_next_winner_d2          (bp@_next_winner_d2[1:0]),
    .bp_nextxbe                 (bp@_nextxbe[3:0]),
    .bp_nextxbe_d1              (bp@_nextxbe_d1[3:0]),
    .bp_nextxbe_d2              (bp@_nextxbe_d2[3:0]),
    .bp_hold_wait_vector                (bp@_hold_wait_vector[5:0]),
    .bp_hold_wait_vector_d1     (bp@_hold_wait_vector_d1[5:0]),
    .bp_select                  (bp@_select),
    .bp_select_d1               (bp@_select_d1),
    .bp_select_d2               (bp@_select_d2),
    .bp_header                  (bp@_header),
    .bp_header_d1               (bp@_header_d1),
    .bp_header_d2               (bp@_header_d2),
    // Inputs
    .lreset_l                   (bp@_lreset_l),
    .bp_arb_enable              (bp@_arb_enable),
    .sop3                       (sop3 & csr_bp1_enable_3),
    .sop2                       (sop2 & csr_bp1_enable_2),
    .sop1                       (sop1 & csr_bp1_enable_1),
    .sop0                       (sop0 & csr_bp1_enable_0),
    ); */
   
   
   FswBypassArbiter bp1 (/*AUTOINST*/
                         // Outputs
                         .bp_grant3             (bp1_grant3),    // Templated
                         .bp_grant2             (bp1_grant2),    // Templated
                         .bp_grant1             (bp1_grant1),    // Templated
                         .bp_grant0             (bp1_grant0),    // Templated
                         .bp_grant_cycle        (bp1_grant_cycle), // Templated
                         .bp_grant_cycle_d1     (bp1_grant_cycle_d1), // Templated
                         .bp_grant_cycle_d2     (bp1_grant_cycle_d2), // Templated
                         .bp_next_winner        (bp1_next_winner[1:0]), // Templated
                         .bp_next_winner_d1     (bp1_next_winner_d1[1:0]), // Templated
                         .bp_next_winner_d2     (bp1_next_winner_d2[1:0]), // Templated
                         .bp_nextxbe            (bp1_nextxbe[3:0]), // Templated
                         .bp_nextxbe_d1         (bp1_nextxbe_d1[3:0]), // Templated
                         .bp_nextxbe_d2         (bp1_nextxbe_d2[3:0]), // Templated
                         .bp_hold_wait_vector   (bp1_hold_wait_vector[5:0]), // Templated
                         .bp_hold_wait_vector_d1(bp1_hold_wait_vector_d1[5:0]), // Templated
                         .bp_header             (bp1_header),    // Templated
                         .bp_header_d1          (bp1_header_d1), // Templated
                         .bp_header_d2          (bp1_header_d2), // Templated
                         .bp_select             (bp1_select),    // Templated
                         .bp_select_d1          (bp1_select_d1), // Templated
                         .bp_select_d2          (bp1_select_d2), // Templated
                         // Inputs
                         .lreset_l              (bp1_lreset_l),  // Templated
                         .sclk                  (sclk),
                         .bp_arb_enable         (bp1_arb_enable), // Templated
                         .sop3                  (sop3 & csr_bp1_enable_3), // Templated
                         .sop3_data             (sop3_data[63:0]),
                         .sop3_bpcontext        (sop3_bpcontext[5:0]),
                         .sop2                  (sop2 & csr_bp1_enable_2), // Templated
                         .sop2_data             (sop2_data[63:0]),
                         .sop2_bpcontext        (sop2_bpcontext[5:0]),
                         .sop1                  (sop1 & csr_bp1_enable_1), // Templated
                         .sop1_data             (sop1_data[63:0]),
                         .sop1_bpcontext        (sop1_bpcontext[5:0]),
                         .sop0                  (sop0 & csr_bp1_enable_0), // Templated
                         .sop0_data             (sop0_data[63:0]),
                         .sop0_bpcontext        (sop0_bpcontext[5:0]),
                         .poolmask              (poolmask[15:0]),
                         .bufbusy_mask          (bufbusy_mask[63:0]));
   
   
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
                       
                       xb0_obx_NextXbe_s3a, // This is unused signal now.
                       xb1_obx_NextXbe_s3a,
                       xb2_obx_NextXbe_s3a,
                       xb3_obx_NextXbe_s3a,
                       
                       syn64,
                       dataout64,
                       
                       1'b0
                       };
   // lint_checking SCX_UNUSED on
   
   
endmodule

module FswBypassArbiter (/*AUTOARG*/
                         // Outputs
                         bp_grant3, bp_grant2, bp_grant1, bp_grant0, bp_grant_cycle, bp_grant_cycle_d1, bp_grant_cycle_d2,
                         bp_next_winner, bp_next_winner_d1, bp_next_winner_d2, bp_nextxbe, bp_nextxbe_d1, bp_nextxbe_d2,
                         bp_hold_wait_vector, bp_hold_wait_vector_d1, bp_header, bp_header_d1, bp_header_d2, bp_select,
                         bp_select_d1, bp_select_d2,
                         // Inputs
                         lreset_l, sclk, bp_arb_enable, sop3, sop3_data, sop3_bpcontext, sop2, sop2_data, sop2_bpcontext,
                         sop1, sop1_data, sop1_bpcontext, sop0, sop0_data, sop0_bpcontext, poolmask, bufbusy_mask
                         ) ;
   
   input        lreset_l;
   input        sclk;
   input        bp_arb_enable;
   output       bp_grant3;
   output       bp_grant2;
   output       bp_grant1;
   output       bp_grant0;
   output       bp_grant_cycle;
   output       bp_grant_cycle_d1;
   output       bp_grant_cycle_d2;
   output [1:0] bp_next_winner;
   output [1:0] bp_next_winner_d1;
   output [1:0] bp_next_winner_d2;
   output [3:0] bp_nextxbe;
   output [3:0] bp_nextxbe_d1;
   output [3:0] bp_nextxbe_d2;
   output [5:0] bp_hold_wait_vector;
   output [5:0] bp_hold_wait_vector_d1;
   output       bp_header;
   output       bp_header_d1;
   output       bp_header_d2;
   output       bp_select;
   output       bp_select_d1;
   output       bp_select_d2;
   input        sop3;
   input [63:0] sop3_data;
   input [5:0]  sop3_bpcontext;
   input        sop2;
   input [63:0] sop2_data;
   input [5:0]  sop2_bpcontext;
   input        sop1;
   input [63:0] sop1_data;
   input [5:0]  sop1_bpcontext;
   input        sop0;
   input [63:0] sop0_data;
   input [5:0]  sop0_bpcontext;
   input [15:0] poolmask;
   input [63:0] bufbusy_mask;
endmodule
