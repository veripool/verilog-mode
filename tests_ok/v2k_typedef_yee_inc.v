`ifdef __TEST_I

`else

 `define __TEST_I

 `ifdef TWO_STATE_LOGIC
typedef bit logic_t;  // Use two-state logic
 `else
typedef logic logic_t;  // Use four-state logic
 `endif

typedef reg   ff_t; // Default F/F type
typedef reg   lat_t; // Default latch type

//----------------------------
// 24 bit wide pixel types
//
typedef union packed {
   logic_t [23:0] bits;
   struct packed {
      logic_t [7:0] red;
      logic_t [7:0] grn;
      logic_t [7:0] blu;
   } color;
} pixel24_t;

`endif
