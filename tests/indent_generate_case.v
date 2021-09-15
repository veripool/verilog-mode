module indent_gen_case #(parameter P = 0)
(input d, output reg q);

case (P)
0: always @(*)
q = d;

1: begin
always @(*)
q = d;
end

2: always @(*) begin
q = d;
end

3: begin
always @(*) begin
q = d;
end
end
endcase

endmodule
