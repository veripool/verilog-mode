module dummy;

   parameter [TSTBITS-1:0] // synopsys enum tstate_info
		TIDLE = 3'b000,
		TCN1  = 3'b001,
		TCN2  = TCN1+1, // must be numbered consecutively
		TCN3  = TCN2+1,
		TCN4  = TCN3+1,
		TCN5  = TCN4+1,
		IOCLR = TCN5+1,
		TUNU1 = 3'b111;

   // state and output logic
   always @ (`ifdef SIMFSM
             ireset or
             `endif
             /*AUTOSENSE*/fooc2_qual or foocr_we or ioclrinst or tstate) begin
      ioclrtmout = 1'b0;
      case (tstate)
	TIDLE: begin
           if (foocr_we)
             ntstate = TCN1;
           else
             ntstate = TIDLE;
	end
	TCN1,TCN2,TCN3,TCN4,TCN5: begin
           if (ioclrinst | fooc2_qual)
             ntstate = TIDLE;
           else
             ntstate = tstate + 1;
	end
	IOCLR: begin
           ntstate = TIDLE;
           ioclrtmout = 1'b1;
	end
	TUNU1: begin
           ntstate = TIDLE;
	     `ifdef SIMFSM
           if (~ireset)
             $display("ERROR: entered unused state at %t",$time);
	     `endif
	end
	default: begin
           ntstate = 'bx;
           ioclrtmout = 1'bx;
	     `ifdef SIMFSM
           if (~ireset)
             $display("ERROR: entered unknown state at %t",$time);
	     `endif
	end
      endcase // case(tstate)
   end // always @ (...

endmodule // dummy
