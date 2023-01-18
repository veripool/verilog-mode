module indent_gen_if #(parameter P = 0)
(input d, output reg q);

generate
if (P == 0) begin
always @(*)
q = d;
end

if (P == 1) begin
always @(*) begin
q = d;
end
end

if (P == 1) begin
always @(*)
q = d;
end
else begin
always @(*)
q = d + 1'b1;
end
endgenerate

endmodule



// Without generate keyword
module indent_gen_if #(parameter P = 0)
(input d, output reg q);


if (P == 0) begin
always @(*)
q = d;
end

if (P == 1) begin
always @(*) begin
q = d;
end
end

if (P == 1) begin
always @(*)
q = d;
end
else begin
always @(*)
q = d + 1'b1;
end


endmodule
