module autoreset_label_gorfajn;
   
   always_ff @(posedge clk or negedge reset)
     if (~reset) begin
        /*AUTORESET*/
        // Beginning of autoreset for uninitialized flops
        a <= 1'h0;
        z <= 1'h0;
        // End of automatics
     end else begin
        a<=b;
        foo: assert (b==4);
        bar: z<=1;
     end
   
endmodule
