module uvm;
class simple_item extends uvm_sequence_item;
   rand int unsigned addr;
   rand int unsigned data;
   rand int unsigned delay;
   constraint c1 { addr < 16'h2000; }
   constraint c2 { data < 16'h1000; }
   // UVM automation macros for general objects
   `uvm_object_utils_begin(simple_item)
      a  = b;
      c  = d;
      `uvm_field_int(addr, UVM_ALL_ON)
      `uvm_field_int(data, UVM_ALL_ON)
      `uvm_field_int(delay, UVM_ALL_ON)
   `uvm_object_utils_end
   // Constructor
   function new (string name = "simple_item");
      super.new(name);
   endfunction : new
endclass : simple_item
class mydata extends uvm_object;
   
   string str;
   mydata subdata;
   int field;
   myenum e1;
   int queue[$];
   `uvm_object_utils(mydata)
   `uvm_object_utils_begin(mydata) //requires ctor with default args
      `uvm_field_string(str, UVM_DEFAULT)
      `uvm_field_object(subdata, UVM_DEFAULT)
      `uvm_field_int(field, UVM_DEC) //use decimal radix
      `uvm_field_enum(myenum, e1, UVM_DEFAULT)
      `uvm_field_queue_int(queue, UVM_DEFAULT)
   `uvm_object_utils_end
   `uvm_object_param_utils_begin(mydata) //requires ctor with default args
      `uvm_field_string(str, UVM_DEFAULT)
      `uvm_field_object(subdata, UVM_DEFAULT)
      `uvm_field_int(field, UVM_DEC) //use decimal radix
      `uvm_field_enum(myenum, e1, UVM_DEFAULT)
      `uvm_field_queue_int(queue, UVM_DEFAULT)
   `uvm_object_utils_end
endclass
class my_trans extends uvm_sequence_item;
   
   rand  bit [127:0]               data [];
   
   //---> Configuration
   `uvm_object_utils_begin(my_trans)
      `uvm_field_array_int ( data, UVM_ALL_ON)
   `uvm_object_utils_end
   
   function new (string name = "my_trans", uvm_sequencer_base        sequencer = null, uvm_sequence parent_seq = null);
      super.new(name, sequencer, parent_seq);
   endfunction : new
endclass : my_trans
endmodule // uvm

module tt;
   
   initial begin
      while (1) begin
         `uvm_do_with(aa, {bb == 0;})
         `uvm_do(cc)
         `uvm_do(cc)
      end // while (1)
   end // initial begin
   
endmodule // tt

