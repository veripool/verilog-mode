module t;
   always_ff @(posedge csclk) begin
      if (~srst_n) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         bar        <= 1'h0;
         foo.addr   <= 1'h0;
         foo.length <= 1'h0;
         foo.ring   <= 1'h0;
         foo.tgt    <= 1'h0;
         // End of automatics
      end
      else begin
         if (dma_req_n2_sk) begin
            foo.tgt <= '{attr  : in_attrib,
                         rsvd  : 2'b0,
                         lst   : in_last,
                         fst   : in_fst,
                         err   : in_err,
                         ring  : in_ring.vrg};
            foo.ring   <= sg_cmd_n2_sk.vfr;
            foo.length <= {3'h0,dma_size_n2_sk};
            bar        <= 1'b1;
         end
         else begin
            foo.addr <= nxt_dma_ptr_sk;
         end
      end
   end
endmodule
