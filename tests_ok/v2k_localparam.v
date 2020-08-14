
// 2001 Parameter Style
module v2k_localparam;
   
   localparam X = 10;
   parameter  Y = 10;
   
   reg        z;
   
   always @ (/*AS*/) begin
      z = X | Y;
   end
   
endmodule
