module a();
always(*)begin
a = #1 b |
c |
d;
a <= #1  b |
c |
d;
a <= # 1  b |
c |
d;

end
endmodule
