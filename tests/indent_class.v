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

 
class A;
   extern function int e1();
   extern function int e2(int src,int dst);
   extern static function int f1();
   extern static function int f2(int src,int dst);
   extern static function int f3(int src,int dst);
   extern static function chandle f10(int src);
   extern static function automatic int f11(int mcid);
   extern function automatic int f13(int mcid);
   static function int s1();
      int i = 0;
   endfunction
   static function int s2();
      int i = 0;
   endfunction
   function int f1();
      int i = 0;
   endfunction
   function int f2();
      int i = 0;
   endfunction
endclass
