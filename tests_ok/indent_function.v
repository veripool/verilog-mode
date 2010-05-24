module t;
   
endmodule
class C;
   function int f();
      f  = 17;
   endfunction
   extern function int g();
   virtual function int f();
      a;
   endfunction // int
   // pure virtual functions have no endfunction.
   C a;
   initial begin
      $display("hello world");
      $display("a of f is %d, g is %d", a.f(),a.g());
   end
   function int C::g();
      g  = 18;
   endfunction // g
   // pure virtual functions have no endfunction.
endclass // C

class pure_virt_func_class;
   pure virtual function string pure_virt_func();
   pure virtual function string pure_virt_func();
   pure virtual function string pure_virt_func();
   extern pure virtual task t();
   pure virtual task t();
   virtual task t();
      /* body */
   endtask // t
   virtual function f();
      /* body */
   endfunction // f
endclass // pure_virt_func_class



