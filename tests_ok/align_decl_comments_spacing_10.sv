// Issue #435
module foo
  (
   // Global Interface Signals
   input clk,                   // core system clock
   input signal1,               // Comment here which should be at "comment-column"
   input signal_long2,          // Comment here which should be at "comment-column"
   input sig3,                  // Here, I've hit "tab" twice and this line is correct
   input s4,                    // Comment here which should be at "comment-column"
   input reset_L,               // module reset: global register
   );
endmodule // foo


// Issue #898
module my_module
  ( input a,           // sig a
    input bc,          // sig bc
    input d            // sig d
    );
   //
endmodule


// Issue #922
module foo
  (input logic  clk,                                           // Added with respect to #922 to test alignment
   input        my_pkg::user_type keep_type_way_left,          //.  <==Keep-indent marker
   output logic done);                                         // Added with respect to #922 to test alignment
   
   import my_pkg::*; // Added with respect to #922 to test alignment
   logic [7:0] city_bus;                                   // Added with respect to #922 to test alignment
   var         user_type keep_type_also_way_left;          //.  <==Keep-indent marker
endmodule


// Issue #1157
module top
  (
   //Inputs
   input            CLK,                //System Clock
   input            RST,                //Active High Reset
   input [3:0]      CONTROL,            //Control decoder.
   
   //Outputs
   output reg [7:0] LIVE_DATA,          //1 byte data
   output           VALID               //Valid Flag
   );
endmodule


// Other tests (some of them not working @ June 2022)
module foo
  (
   // This comment should NOT get aligned
   input logic       a1,          // comment
   input logic [1:0] a2,          //comment
   input logic       a3,
   input logic       a4,
   input logic [1:0] a5,          //comment
   output logic      z1,          //    comment
   input logic [1:0] z2           /* comment */
   // This comment should NOT get aligned
   );
   
   localparam  IDLE = 0,          // '01
               READ = 1,// '02
               THINK = 2,// '04
               SEND = 3,// '08
               WAIT = 4,// '10
               GET_ACK = 5,// '20
               WAIT_BUS = 6;// '40
   
   // This comment should NOT get aligned
   logic       s1;                // comment
   logic [1:0] s2;                //comment
   logic       s3;
   logic       s4;
   logic [1:0] s5;                //comment
   logic       t1;                //    comment
   logic [1:0] t2;                /* comment */
   logic [1:0] /* embedded comment should NOT get aligned */ t3;
   // This comment should NOT get aligned
   /* This multiline comment
    should NOT get aligned */
endmodule

// Local Variables:
// verilog-align-comment-distance: 10
// End:

