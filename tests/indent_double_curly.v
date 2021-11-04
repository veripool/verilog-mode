module test;
always_ff @(posedge clk or negedge rst_n)
    if (~rst_n)
begin
 a <= {(5){1'b0}};
     a <= 1;
   end

always_ff @(posedge clk or negedge rst_n)
if (~rst_n)
     begin
   a <= {5{1'b0}};
 a <= 1;
      end

always_ff @(posedge clk or negedge rst_n)
  if (~rst_n)
    begin
      a <= {{1'b0,1'b0}};
a <= 1;
 end

always_ff @(posedge clk or negedge rst_n)
  if (~rst_n)
   begin
       a <= {b, {1'b0,1'b0}};
 a <= 1;
        end

always_ff @(posedge clk or negedge rst_n)
    if (~rst_n)
     begin
  a <= {b[1:0], {1'b0,1'b0}};
   a <= 1;
       end
  endmodule
