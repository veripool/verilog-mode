module batch_li_child
  #(parameter
    
    WIDTH_0= 'h8,
    WIDTH_1 = 'h4
    )
   (
    input rst,
    input clk
    );
   
   reg [WIDTH_0-1:0] counter_0;
   reg [WIDTH_1-1:0] counter_1;
   
   always @(posedge clk) begin
      if (rst) begin
         counter_0 <= #1 0;
         counter_1 <= #1 0;
      end
      else begin
         counter_0 <= #1 counter_0 + 1'b1;
         counter_1 <= #1 counter_1 + 1'b1;
      end
   end
   
endmodule

