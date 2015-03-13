// bug 895 - labeling of always constructs
module example;

always
begin
end

always @(posedge clk)
begin
end

always @*
begin
end

always @(*)
begin
end // always @ (*)

always_comb
begin
end

always_latch
begin
end

always @( *)
begin
end

always @(* )
begin
end

always_ff @(posedge clk)
begin
end

always @(*)
begin
end // garbage

endmodule

// Local Variables:
// verilog-minimum-comment-distance: 1
// verilog-auto-endcomments: t
// End:
