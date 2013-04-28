module ovm;
class simple_item extends ovm_sequence_item;
   rand int unsigned addr;
   rand int unsigned data;
   rand int unsigned delay;
   constraint c1 { addr < 16'h2000; }
   constraint c2 { data < 16'h1000; }
   // OVM automation macros for general objects
   `ovm_object_utils_begin(simple_item)
      a  = b;
      c  = d;
      `ovm_field_int(addr, OVM_ALL_ON)
      `ovm_field_int(data, OVM_ALL_ON)
      `ovm_field_int(delay, OVM_ALL_ON)
   `ovm_object_utils_end
   // Constructor
   function new (string name = "simple_item");
      super.new(name);
   endfunction : new
endclass : simple_item
class mydata extends ovm_object;
   
   string str;
   mydata subdata;
   int field;
   myenum e1;
   int queue[$];
   `ovm_object_utils(mydata)
   `ovm_object_utils_begin(mydata) //requires ctor with default args
      `ovm_field_string(str, OVM_DEFAULT)
      `ovm_field_object(subdata, OVM_DEFAULT)
      `ovm_field_int(field, OVM_DEC) //use decimal radix
      `ovm_field_enum(myenum, e1, OVM_DEFAULT)
      `ovm_field_queue_int(queue, OVM_DEFAULT)
   `ovm_object_utils_end
   `ovm_object_param_utils_begin(mydata) //requires ctor with default args
     `ovm_field_string(str, OVM_DEFAULT)
      `ovm_field_object(subdata, OVM_DEFAULT)
      `ovm_field_int(field, OVM_DEC) //use decimal radix
      `ovm_field_enum(myenum, e1, OVM_DEFAULT)
      `ovm_field_queue_int(queue, OVM_DEFAULT)
   `ovm_object_utils_end
endclass
class my_trans extends ovm_sequence_item;
   
   rand  bit [127:0]               data [];
   
   //---> Configuration
   `ovm_object_utils_begin(my_trans)
      `ovm_field_array_int ( data, OVM_ALL_ON)
   `ovm_object_utils_end
   
   function new (string name = "my_trans", ovm_sequencer_base        sequencer = null, ovm_sequence parent_seq = null);
      super.new(name, sequencer, parent_seq);
   endfunction : new
endclass : my_trans
endmodule // ovm

module tt;
   
   initial begin
      while (1) begin
         `ovm_do_with(aa, {bb == 0;})
         `ovm_do(cc)
         `ovm_do(cc)
      end // while (1)
   end // initial begin
   
endmodule // tt

