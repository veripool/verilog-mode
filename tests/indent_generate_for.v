module indent_gen_for #(parameter P = 1)
(input d, output reg q);

genvar i;
generate
for (i = 0; i < P; i += 1) begin
always @(*) begin
q = d;
end
end

for (i = 0; i < P; i += 1) begin
always @(*)
q = d;
end
endgenerate

endmodule




// Without generate keyword
module indent_gen_for #(parameter P = 1)
(input d, output reg q);

genvar i;

for (i = 0; i < P; i += 1) begin
always @(*) begin
q = d;
end
end

for (i = 0; i < P; i += 1) begin
always @(*)
q = d;
end


endmodule
