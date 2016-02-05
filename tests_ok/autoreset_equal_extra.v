module autoreset_equal_extra ();
   
   always_ff @(posedge csclk) begin
      if( ~srst_n | !val_tx_to_csi ) begin
         csi.cmd <= ncbo_cmd_t'('0);
         // vvvvvv   fifo.data.cb_req.req.cmd = '0;  should not be below
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         csi.src <= 1'h0;
         csi.wr  <= 1'h0;
         // End of automatics
      end
      else begin
         if (fifo.sot) begin
            csi.src                               <= fifo.src;
            csi.wr                                <= (fifo.data.cb_req.req.cmd == ncb_defs::NCBO_RSVD_LMTST
                       | fifo.data.cb_req.req.cmd == ncb_defs::NCBO_IOBST
                                                      );
            csi.cmd <= fifo.data.cb_req.req.cmd;
         end
      end
   end
   
   always_ff @(posedge csclk) begin
      if (~srst_n) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         sdp__x2p.bval <= 1'h0;
         sdp__x2p.err  <= 1'h0;
         // End of automatics
      end
      else begin
         sdp__x2p.err <= (x2p_fifo_rdat.err & x2p_fifo_pop_d3_sk)
           ? x2p_p2x_roc_rtl_pkg::X2P_PKT_ERR_RCVERR
                         : x2p_p2x_roc_rtl_pkg::X2P_PKT_ERR_NONE;
         sdp__x2p.bval <= x2p_fifo_rdat.bval & {4{x2p_fifo_pop_d3_sk}};
         //FOO::bar <= 1;  // Legal, though not typically used in RTL
      end
   end
   
endmodule
