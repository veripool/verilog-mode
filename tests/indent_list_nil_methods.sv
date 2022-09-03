class test;

virtual function void func1 (
input bit [8:0] in1,
input bit in2,
ref example_t ref1,
ref bit [17:0] ref2 [],
ref bit [15:0] ref3 [],
example_t ex1,
input bit in3 = 1'b0,
output bit [17:0] out1
);
out1 = {in1[7:0], in1[7:0]};
endfunction

virtual task task1 (
input bit [8:0] in1,
input bit in2,
ref example_t ref1,
ref bit [17:0] ref2 [],
ref bit [15:0] ref3 [],
example_t ex1,
input bit in3 = 1'b0,
output bit [17:0] out1
);
out1 = {in1[7:0], in1[7:0]};
endtask

virtual task task1 (input bit [8:0] in1,
input bit in2,
ref example_t ref1,
ref bit [17:0] ref2 [],
ref bit [15:0] ref3 [],
example_t ex1,
input bit in3 = 1'b0,
output bit [17:0] out1
);
out1 = {in1[7:0], in1[7:0]};
endtask

virtual task task1 (input bit [8:0] in1, input bit in2, ref example_t ref1,
ref bit [17:0] ref2 [],
ref bit [15:0] ref3 [],
example_t ex1,
input bit in3 = 1'b0,
output bit [17:0] out1
);
out1 = {in1[7:0], in1[7:0]};
endtask

virtual task task1 (  input bit [8:0] in1, input bit in2, ref example_t ref1,
ref bit [17:0] ref2 [],
ref bit [15:0] ref3 [],
example_t ex1,
input bit in3 = 1'b0,
output bit [17:0] out1
);
out1 = {in1[7:0], in1[7:0]};
endtask

virtual task task1 (  input bit [8:0] in1, input bit in2, ref example_t ref1,
ref bit [17:0] ref2 [],
ref bit [15:0] ref3 [],
example_t ex1,
input bit in3 = 1'b0,
output bit [17:0] out1);
out1 = {in1[7:0], in1[7:0]};
endtask

virtual task task1 (input bit [8:0] in1, input bit in2, ref example_t ref1);
out1 = {in1[7:0], in1[7:0]};
endtask

protected function void func2 (
input bit in,
output bit [3:0] out
);
out = |in;
endfunction

protected task task2 (
input bit in,
output bit [3:0] out
);
out = |in;
endtask

protected task task2 (input bit in,
output bit [3:0] out
);
out = |in;
endtask

protected task task2 ( input bit in,
output bit [3:0] out
);
out = |in;
endtask

protected task task2 ( input bit in,
output bit [3:0] out);
out = |in;
endtask

protected task task2 (input bit in, output bit [3:0] out);
out = |in;
endtask

static function void func3 (
input bit in,
output bit [3:0] out
);
out = |in;
endfunction

static task task3 (
input bit in,
output bit [3:0] out
);
out = |in;
endtask

static task task3 (input bit in,
output bit [3:0] out
);
out = |in;
endtask

static task task3 ( input bit in,
output bit [3:0] out
);
out = |in;
endtask

static task task3 ( input bit in,
output bit [3:0] out  );
out = |in;
endtask

static task task3 (input bit in, output bit [3:0] out  );
out = |in;
endtask

function void func4 (
input bit in,
output bit [3:0] out
);
out = &in;
endfunction

task task4 (
input bit in,
output bit [3:0] out
);
out = &in;
endtask

task task4 (input bit in,
output bit [3:0] out
);
out = &in;
endtask

task task4 ( input bit in,
output bit [3:0] out
);
out = &in;
endtask

task task4 ( input bit in,
output bit [3:0] out);
out = &in;
endtask

task task4 (input bit in, output bit [3:0] out);
out = &in;
endtask

endclass

// Local Variables:
// verilog-indent-lists: nil
// verilog-align-typedef-regexp: "\\<[a-zA-Z_][a-zA-Z_0-9]*_t\\>"
// End:
