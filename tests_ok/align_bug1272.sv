// Issue #1272

import bar_pkg1::*;
import foo_pkg1::*;

module alignment_test
  import bar_pkg2::*;
   import foo_pkg2::*;
   #(
     parameter DATA_WIDTH = 8,
     parameter ADDR_WIDTH = 4
     )
   (
    input wire                  clk,
    input wire                  res_n,
    input wire                  valid,
    input wire [DATA_WIDHT-1:0] data_in,
    input wire [ADDR_WIDTH-1:0] addr,
    output logic                accept
    );
   
   import bar_pkg3::*;
   import foo_pkg3::*;
   
   localparam             LP_BAR_0   = 1;
   localparam             LP_BAR_100 = 100;
   localparam logic [3:0] LP_BAR_5   = 5;
   
endmodule

// Local Variables:
// verilog-auto-lineup: all
// End:
