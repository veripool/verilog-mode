module foo;
   
   reg [1:0] a;
   
   assert property (@(posedge clk) e |-> f);
   
   reg [1:0] b;
   
   always @(posedge clk, negedge rst)
     if (~rst) begin
        /*AUTORESET*/
        // Beginning of autoreset for uninitialized flops
        a <= 2'h0;
        b <= 2'h0;
        // End of automatics
     end
     else begin
        a<=b;
        b<=a;
     end
   
endmodule
