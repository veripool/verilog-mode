class foo();
 int my_field;
endclass // foo

class temp;
 extern function test();
 extern function test2();
 function foo();
 foo = 1;
 endfunction // foo
 extern function test3();
 reg [31:0] b;
endclass // temp

class short extends temp;
 logic a;
endclass

`define vmm_channel(A) A+A


module foo;
 reg a;
 reg [1:0] b;

 initial begin
 b = `vmm_channel(a);
 end // initial begin
endmodule // foo

 
