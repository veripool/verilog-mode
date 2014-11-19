// bug 825
module x;

always @*
begin
end

initial
begin
end

final
begin
end

initial forever
  begin
end

foreach(1)
begin
  end

do
 begin
 end while (i);

initial @a.b
  begin
end

always @E
  begin
 end

forever @E
 begin
  end

endmodule

// Local Variables:
// verilog-indent-begin-after-if: nil
// End:
