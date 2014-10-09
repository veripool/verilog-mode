module toto (input logic dummy);
   import "DPI-C" pure function real fabs (input real a);
   import "DPI-C" context function real fcons (input real a);
   import "DPI-C" string_sv2c = task string();
   import "DPI-C" int_sv2c = task intsv2c();
   import "DPI-C" context int_sv2c = task intsv2cont();
   logic a; // wrong indentation
endmodule // wrong indentation
