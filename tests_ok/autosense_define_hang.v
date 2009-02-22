//From: Anup Sharma <asharma@Eng.Sun.COM>

module x;
   
   always @ (/*AS*/`EC_EXCLU or `EC_SHARE or jpack_share) begin
      jb_mc_xact_state_a1[2:0] <= #1 jpack_share[7] ? `EC_SHARE : `EC_EXCLU;
   end
endmodule
