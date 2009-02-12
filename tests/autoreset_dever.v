module x;
   always @(posedge piclk) begin
      if (k_i_reset) begin
	 /*AUTORESET*/
      end
      else begin
	 idat_ICErrData_i3 <= idat_way0_i2[1*OPCWID-1:0*OPCWID];
      end
   end
endmodule
