module autoreset_label_gorfajn;

   always_ff @(posedge clk or negedge reset)
     if (~reset) begin
       /*AUTORESET*/
     end else begin
       a<=b;
       foo: assert (b==4);
       bar: z<=1;
     end

endmodule
