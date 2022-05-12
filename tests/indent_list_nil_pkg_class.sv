package foo;

class A;
rand int attribute1;
rand logic [3:0] attribute2;

constraint values_c {
attribute1 inside {[0:a]};
attribute2 inside {[0:15]};
}

function new (
int a,
logic [3:0] b
);
this.attribute1 = a;
this.attribute2 = b;
endfunction: new

task T1 (
input int a,
input logic [3:0] b
);
this.attribute1 = a;
this.attribute2 = b;
endtask: T1

endclass // A

endpackage // foo


// Local Variables:
// verilog-indent-lists: nil
// End:
