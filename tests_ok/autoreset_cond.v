module x;
   reg [1:0] idx_sel_2a;
   always @(posedge usclk or negedge srst_0a_n) begin
      if (~srst_0a_n) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         bar <= 1'h0;
         foo <= 1'h0;
         // End of automatics
      end
      else begin
         foo                <= idx_adr_1a[1:0];
         bar                <= (idx_sel_2a == 2'h0 ? idx_rd_dat0_2a[12:0] :
                 idx_sel_2a == 2'h1 ? idx_rd_dat1_2a[12:0] :
                 idx_sel_2a == 2'h2 ? idx_rd_dat2_2a[12:0] :
                                /**/                 idx_rd_dat3_2a[12:0]);
      end
   end
   
endmodule
