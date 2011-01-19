package pkg;
   typedef logic [1:0] my_type;
endpackage
   
module top;
   import pkg::*;
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   pkg::my_type_t       a;                      // From sub_2 of sub_2.v
   pkg::my_type_t       z;                      // From sub_1 of sub_1.v
   // End of automatics
   sub_1 sub_1 (.*,
                // Outputs
                .z                      (z),                     // Implicit .*
                // Inputs
                .a                      (a));                    // Implicit .*
   sub_2 sub_2 (.*,
                // Outputs
                .a                      (a),                     // Implicit .*
                // Inputs
                .z                      (z));                    // Implicit .*
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
