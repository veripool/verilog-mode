`default_nettype none

package testcase_pkg;
   
   typedef int unsigned uint;
   
   localparam uint SIZE  = 8;
   
   typedef enum {ENUM1, ENUM2} enum_t;
   
endpackage
   
module testcase_top
  (
   input                                 testcase_pkg::enum_t top_enum,
   input logic [testcase_pkg::SIZE-1:0]  top_in,
   output logic [testcase_pkg::SIZE-1:0] top_out
   );
   import testcase_pkg::*;
   //enum_t sub_enum; // is not declared by AUTOWIRE
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   testcase_pkg::enum_t sub_enum;               // From testcase_sub1 of testcase_sub1.v
   logic [testcase_pkg::SIZE-1:0] sub_in; // From testcase_sub1 of testcase_sub1.v
   logic [testcase_pkg::SIZE-1:0] sub_out;      // From testcase_sub2 of testcase_sub2.v
   // End of automatics
   assign top_out  = sub_out;
   testcase_sub1 testcase_sub1 (.*,
                                // Outputs
                                .sub_enum       (sub_enum),      // Implicit .*
                                .sub_in         (sub_in[testcase_pkg::SIZE-1:0]), // Implicit .*
                                // Inputs
                                .top_enum       (top_enum));     // Implicit .*
   testcase_sub2 testcase_sub2 (.*,
                                // Outputs
                                .sub_out                (sub_out[testcase_pkg::SIZE-1:0]), // Implicit .*
                                // Inputs
                                .sub_enum       (sub_enum),      // Implicit .*
                                .sub_in         (sub_in[testcase_pkg::SIZE-1:0])); // Implicit .*
endmodule

module testcase_sub1
  (
   input                                 testcase_pkg::enum_t top_enum,
   output                                testcase_pkg::enum_t sub_enum,
   output logic [testcase_pkg::SIZE-1:0] sub_in
   );
   import testcase_pkg::*;
   assign sub_enum  = top_enum;
   assign sub_in  = '1;
endmodule

module testcase_sub2
  (
   input                                 testcase_pkg::enum_t sub_enum,
   input logic [testcase_pkg::SIZE-1:0]  sub_in,
   output logic [testcase_pkg::SIZE-1:0] sub_out
   );
   import testcase_pkg::*;
   assign sub_out  = (sub_enum==ENUM1) ? ~sub_in : sub_in;
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// verilog-auto-star-save: t
// End:
