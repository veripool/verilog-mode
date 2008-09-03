module autoascii_peltan
  (
   input        test,
   output [1:0] test_out
   );

`include "autoascii_peltan_inc.v"

   wire [3:0] 	/* synopsys enum xstate */
            xstate;

   /* synopsys translate off */

   /*AUTOASCIIENUM("xstate", "v_xstate")*/
   // Beginning of automatic ASCII enum decoding
   reg [47:0]		v_xstate;		// Decode of xstate
   always @(xstate) begin
      case ({xstate})
	state1:   v_xstate = "state1";
	state0:   v_xstate = "state0";
	default:  v_xstate = "%Error";
      endcase
   end
   // End of automatics

   /* synopsys translate on */

endmodule // sample

// Local Variables:
// verilog-library-directories:(".")
// eval:(verilog-read-includes)
// End:
