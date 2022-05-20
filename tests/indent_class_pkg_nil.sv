package foo;

typedef logic [7:0] byte_t;
localparam byte_t ALL_ONES = 8'hFF;

function foo3 (input int a);
$display(a);
endfunction

class A;
    byte_t foo2 = ALL_ONES;
endclass

endpackage

// Local Variables:
// verilog-indent-class-inside-pkg: nil
// End:
