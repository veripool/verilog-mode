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

class base_test extends uvm_test;
   `uvm_component_utils(base_test)
   typedef virtual my_if my_vif_t;
   // A function definition starting with the virtual keyword should not be
   // detected as a declaration. This issue is seen when an attempt to indent
   // each declaration is done (when the verilog-auto-lineup variable is set
   // to 'declarations).
   //   In other words, the "function" in "virtual function" below must not be
   // aligned with "my_if" in the "typedef virtual my_if.." line above.
   virtual function void start_of_simulation_phase(uvm_phase phase);
      super.start_of_simulation_phase(phase);
   endfunction : start_of_simulation_phase
endclass : base_test
