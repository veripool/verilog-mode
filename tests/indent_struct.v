module foo;
   
   a = { g + c; };
   a = c;
   
   typedef struct {
      reg 	  r;
      ahb_op_t         op;             // Read, write, etc.
      ahb_cycle_type_t cti;            // Cycle type for bursts
      ahb_incr_type_t  incr;           // Increment type (for bursts)
      bit 	  b;
      reg 	  r;
      ahb_thingy a;
      bit [31:2]  addr;           // Starting address
      bit [3:0]   byte_sel;       // Byte lane select
      int 	  len;            // Length of transfer
      bit [31:0]  data[0:7];      // Write data
   } ahb_req_t;
   
   struct 	  {
      reg 	  f;
      xyzzy b;
   };
   struct 	  packed {
      int 	  a;  // ok
   };
   struct 	  packed signed {
      int 	  a;  // woops
   };
   struct 	  packed unsigned {
      int 	  a;  // woops
   };
   
endmodule // foo

module foo (
    input a;
    input c;
    output d;
	    );
   always @(a) g;
   
   

endmodule // foo
