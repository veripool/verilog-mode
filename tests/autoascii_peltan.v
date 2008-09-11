module autoascii_peltan
  (
   input        test,
   output [1:0] test_out
   );

`include "autoascii_peltan_inc.v"

   // Duplicate of what's in _inc
   localparam [3:0] /* synopsys enum xstate */
	    state0 = 4'h0;

   wire [3:0] 	/* synopsys enum xstate */
            xstate;

   /* synopsys translate off */

   /*AUTOASCIIENUM("xstate", "v_xstate")*/

   /* synopsys translate on */

endmodule // sample

// Local Variables:
// verilog-library-directories:(".")
// eval:(verilog-read-includes)
// End:
