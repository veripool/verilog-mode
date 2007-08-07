`ifndef FOO
 `define FOO
module foo;
   reg [31:0] payload [255:0];
   reg [7:0]  index;
   
   always @ (b) begin
      foreach (1) begin
	 @(router.cb);
      end // foreach (1)
   end // always @ (b)
endmodule // foo
`else // !`ifndef FOO
`endif // !`ifndef FOO
