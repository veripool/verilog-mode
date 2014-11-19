//bug844
module device(
	      input 		 clk,
	      output logic [7:0] Q, out0,
	      output logic 	 pass, fail
	      input [7:0] 	 D, in0,in1 );

   enum 			 logic [2:0] {IDLE, START, RUN, PASS, FAIL } state, next_state;
   logic 			 ready, next_ready;
   logic 			 next_pass, next_fail;

   always_ff @(posedge clk, negedge rstn)
     if (!rstn) begin
	state <= IDLE;
	/*AUTORESET*/
     end
     else begin
	state <= next_state;
	ready <= next_ready;
	pass <= next_pass;
	fail <= next_fail;
     end

   always @* begin
      if (!ready) begin
	 /*AUTORESET*/
      end
      else begin
	 out0 = sel ? in1 : in0;
      end
   end

   always_comb begin
      next_state = state;
      /*AUTORESET*/
      case (state)
	IDLE :	begin
	   // stuff ...
	end
	/* Other states */
	PASS:	begin
	   next_state = IDLE;
	   // stuff ...
	   next_pass = 1'b1;
	   next_ready = 1'b1;
	end
	FAIL:	begin
	   next_state = IDLE;
	   // stuff ...
	   next_fail = 1'b1;
	end
      endcase
   end

   always_latch begin
      if (!rstn) begin
	 /*AUTORESET*/
      end
      else if (clk) begin
	 Q <= D;
      end
   end
endmodule
