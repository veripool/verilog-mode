module myassert(input clk, 
		input reset, 
		input [15:0] data);
   
   property myproperty;
      @(posedge clk)
	$rose(reset) |-> data == 16'h0;
   endproperty
   
   //Assert, cover, and assume property statements
   //support begin/end keywords.  The else begin/end
   //clause below is getting indented improperly.
   myassert0: assert property(myproperty) begin
      $display("myassert0 was successful");
   end
else begin
   $fatal("myassert0 was unsuccessful");
end

   //Also, any statements following the assert,
   //cover, and assume property statements get
   // indented too far to the right.
   always @(posedge clk) begin
   end
endmodule

// https://github.com/veripool/verilog-mode/issues/1836
module tb1;
 a: restrict property (1);
   b: assume property (1);
     c: assume property (1);
       endmodule

// https://github.com/veripool/verilog-mode/issues/1837
module tb2;
         a: cover sequence (1);
     b: cover property (1);
  c: cover property (1);
endmodule
