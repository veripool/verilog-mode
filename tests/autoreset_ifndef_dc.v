module x;
   always @(posedge clk or negedge reset_l) begin
      if (!reset_l) begin
         c <= 1;
         /*AUTORESET*/
      end
      else begin
         a <= in_a;
         b <= in_b;
         c <= in_c;
`ifndef DC
    x <= 1'b1;
`endif
      end
   end
endmodule
