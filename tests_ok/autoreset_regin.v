module autoreset_regin;
   /*AUTOREGINPUT*/
   // Beginning of automatic reg inputs (for undeclared instantiated-module inputs)
   reg [7:0] a;                 // To bar of bar.v
   // End of automatics
   
   bar bar
     (
      /*AUTOINST*/
      // Inputs
      .a                                (a[7:0]));
   
   always @(posedge clk) begin
      if (rst) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         a <= 8'h0;
         // End of automatics
      end
      else begin
         a <= 8'h42;
      end
   end
endmodule

module bar
  input [7:0]    a;
endmodule
