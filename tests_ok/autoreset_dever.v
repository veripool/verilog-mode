module x;
   always @(posedge piclk) begin
      if (k_i_reset) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         idat_ICErrData_i3 <= 1'h0;
         // End of automatics
      end
      else begin
         idat_ICErrData_i3 <= idat_way0_i2[1*OPCWID-1:0*OPCWID];
      end
   end
   
   // 2010-04-08
   localparam MPND  = 5;
   always @(posedge usclk)
     if (~sso_srst_n) begin
        /*AUTORESET*/
        // Beginning of autoreset for uninitialized flops
        rd_dat_s4 <= 1'h0;
        sel_s3    <= 1'h0;
        // End of automatics
     end
     else begin
        sel_s3    <= adr_s2[MIDX];
        rd_dat_s4 <= (sel_s3 == 1'h0 ? rd_dat0_s3[MPND:0]
                      :                rd_dat1_s3[MPND:0]);
     end
   
endmodule
