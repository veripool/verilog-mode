module ExampReset ();
   always @(posedge clk or negedge reset_l) begin
      if (!reset_l) begin
         c <= 1;
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         a <= 1'h0;
         b <= 1'h0;
         // End of automatics
      end
      else begin
         a <= in_a;
         b <= in_b;
         c <= in_c;
      end
   end
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
