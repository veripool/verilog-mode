module sm (/*AUTOARG*/
   // Outputs
   state_e1, state_r
   );

   output [2:0] state_e1;
   output [2:0] state_r;

   //== State enumeration
   parameter [2:0] // synopsys enum state_info
		SM_IDLE =  3'b000,
		SM_ACT = 3'b010;
   //== State variables
   reg [2:0] 	   /* synopsys enum state_info */
		   state_r;		/* synopsys state_vector state_r */
   reg [2:0] 	   /* synopsys enum state_info */
		   state_e1;

   //== ASCII state decoding

   /*AUTOASCIIENUM("state_r", "_stateascii_r", "sm_")*/
   // Beginning of automatic ASCII enum decoding
   reg [31:0]		_stateascii_r;		// Decode of state_r
   always @(state_r) begin
      case ({state_r})
	SM_IDLE:  _stateascii_r = "idle";
	SM_ACT:   _stateascii_r = "act ";
	default:  _stateascii_r = "%Err";
      endcase
   end
   // End of automatics

endmodule
