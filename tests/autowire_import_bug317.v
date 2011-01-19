package pkg;
  typedef logic [1:0] my_type;
endpackage

module top;
  import pkg::*;
  /*AUTOWIRE*/
  sub_1 sub_1 (.*);
  sub_2 sub_2 (.*);
endmodule

module sub_1
  import pkg::*; // bug317
  (
   input  pkg::my_type_t a,
   output pkg::my_type_t z
   );
endmodule

module sub_2
  (
   input  pkg::my_type_t z,
   output pkg::my_type_t a
   );
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// verilog-auto-star-save: t
// End:
