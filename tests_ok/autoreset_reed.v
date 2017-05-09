module x;
   reg a;
   reg b;
   reg c;
   always @(/*AUTOSENSE*/a or b or rst) begin
      if ( rst ) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         c = 1'h0;
         // End of automatics
      end
      else begin
         if ( a <= b ) begin
            c = a;
         end
         else begin
            c = b;
         end
      end
   end
   
   always @ (posedge a) begin
      if ( rst ) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         c <= 1'h0;
         // End of automatics
      end
      else if ( a <= b ) begin
         c <= a;
      end
   end
   
endmodule
