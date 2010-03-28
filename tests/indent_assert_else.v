module myassert(input clk,
                input        reset,
                input [15:0] data);
   
   property myproperty;
      @(posedge clk)
        $rose(reset) |-> data  == 16'h0;
   endproperty
   
   //Assert, cover, and assume property statements
   //support begin/end keywords.  The else begin/end
   //clause below is getting indented improperly.
   myassert0: assert property(myproperty) begin
      $display("myassert0 was successful");
      a;
      b;
      c;
      d;
   end // myassert0: assert property (myproperty)
   else begin
      $fatal("myassert0 was unsuccessful");
   end // else: !assert property(myproperty)
   if (a) begin
      b;
      c;
   end // if (a)
   else begin
      o;
   end // else: !if(a)
   assert (a) begin
      o;
   end // assert (a)
   else begin
      o;
   end // else: !assert (a)
   
   assert (statement) begin
      $display("assertion passed"); //this code is correctly indented
   end // assert (statement)
   else begin // this whole section should be moved to the left
      $error("assertion failed");
   end // else: !assert (statement)
   
   //Also, any statements following the assert,
   //cover, and assume property statements get
   // indented too far to the right.
   always @(posedge clk) begin
      a;
   end // always @ (posedge clk)
endmodule
