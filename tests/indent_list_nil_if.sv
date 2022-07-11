// Issue #1774

module foo (
);

function int foo2 (input a,
output b);

if (some_long_name * some_other_long_name &&
something_here < something_else &&
something_here < something_else) begin
b = a;
end

if ((some_long_name * some_other_long_name &&
something_here < something_else &&
something_here < something_else)) begin
b = a;
end

if ((      some_long_name * some_other_long_name &&
something_here < something_else &&
something_here < something_else
)) begin
b = a;
end

if (
some_long_name * some_other_long_name &&
something_here < something_else &&
something_here < something_else
) begin
b = a;
end

if (some_long_name * some_other_long_name && something_here < something_else && something_here < something_else) begin
b = a;
end else if ( some_condition  ) begin
b = 0;
end
else begin
b = 1;
end

if (   some_long_name * some_other_long_name && something_here < something_else && something_here < something_else
) begin
b = a;
end else if (
some_condition
) begin
b = 0;
end
else begin
b = 1;
end

endfunction // foo2

endmodule // foo

// Local Variables:
// verilog-indent-lists: nil
// End:
