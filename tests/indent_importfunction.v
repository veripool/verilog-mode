module toto (input logic dummy);
   import "DPI-C" pure function real fabs (input real a);
   import "DPI-C" context function real fabs (input real a);
   logic a; // wrong indentation
endmodule // wrong indentation
