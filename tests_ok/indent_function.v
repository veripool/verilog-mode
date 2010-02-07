module t;
class C;
   function int f();
      f  = 17;
   endfunction
   extern function int g();
   virtual function int f();
      a;
   endfunction // int
   
   integer      foo;
endclass // C
   C a;
   initial begin
      $display("hello world");
      $display("a of f is %d, g is %d", a.f(),a.g());
   end
   function int C::g();
      g  = 18;
   endfunction
endmodule
