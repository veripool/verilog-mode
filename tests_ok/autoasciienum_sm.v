module sm (/*AUTOARG*/
   // Outputs
   state_r,
   // Inputs
   clk, rst_
   );

   //==================== Constant declarations ==============

   parameter [2:0]	// synopsys enum state_info
		IDLE = 		3'b000,
		SEND =		3'b001,
		WAIT1 = 		3'b010,
		UPDATE1 = 	3'b011,
		WAIT2 = 		3'b100;

   parameter [2:0] 	/* synopsys enum state_info */ UPDATE2 = 3'b101;

   parameter [2:0] 	NOT_A_STATE_ELEMENT = 3'b101;

   parameter [2:0] 	/* synopsys enum other */
		A_OTHER_STATE_ELEMENT = 3'b101;

   //==================== Input Signals ======================

   input 		clk;			// System clock signal
   input 		rst_;

   //==================== Output Signals =====================

   // s_ynopsys requires the enum comment between the keyword and the symbol While this seems silly,
   // verilog requires this also to avoid misleading people that also use their tools.

   output [2:0] 	state_r;		// SM State information (to GPF)

   //==================== Intermediate Variables =============

   reg [2:0] 		/* synopsys enum state_info */	state_r;		/* synopsys state_vector state_r */
   reg [2:0] 		/* synopsys enum state_info */	state_e1;		// next state of state-machine

   //==================== Code Begin =========================

   always @(/*AUTOSENSE*/state_r) begin
      case(state_r) // synopsys full_case parallel_case
	IDLE: begin
	   state_e1 = SEND;
	end
	SEND: begin
	   state_e1 = WAIT1;
	end
	WAIT1: begin
	   state_e1 = UPDATE1;
	end
	UPDATE1: begin
	   state_e1 = UPDATE2;
	end
	WAIT2: begin
	   state_e1 = UPDATE2;
	end

	UPDATE2: begin
	   state_e1 = IDLE;
	end
	default:	state_e1 = state_r;
      endcase
   end

   always @(posedge clk or negedge rst_) begin
      if (~rst_) begin
	 state_r <= #0 IDLE;
      end
      else begin
	 state_r <= #0 state_e1;
      end
   end

   //==================== DEBUG ASCII CODE =========================

   /*AUTOASCIIENUM("state_r", "_stateascii_r")*/
   // Beginning of automatic ASCII enum decoding
   reg [55:0]		_stateascii_r;		// Decode of state_r
   always @(state_r) begin
      case ({state_r})
	IDLE:     _stateascii_r = "idle   ";
	SEND:     _stateascii_r = "send   ";
	WAIT1:    _stateascii_r = "wait1  ";
	UPDATE1:  _stateascii_r = "update1";
	WAIT2:    _stateascii_r = "wait2  ";
	UPDATE2:  _stateascii_r = "update2";
	default:  _stateascii_r = "%Error ";
      endcase
   end
   // End of automatics

endmodule
