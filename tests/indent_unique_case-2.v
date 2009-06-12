module testmod ();
   always_comb begin
      unique case (eeee)
        ZERO[1:0] : begin
           a = 1;
        end // case: ZERO[1:0]
	
	ONE[1:0] : begin
           a = 1;
	end // case: ONE[1:0]
	
	TWO[1:0] : begin
           a = 1;
	end // case: TWO[1:0]
	THREE[1:0] : begin
           a = 1;
	end // case: THREE[1:0]
      endcase // unique case (eeee)
   end // always_comb
   
   always_ff @ (posedge clk) begin
      if (reset) begin
         current_state <= `TQ STATE0;
      end // if (reset)
      else begin
         priority case (current_state)
           STATE0 : begin
              current_state <= `TQ STATE3;
           end // case: STATE0
	   
           STATE1 : begin
              current_state <= `TQ STATE3;
           end // case: STATE1
	   
           STATE2 : begin
              current_state <= `TQ STATE3;
           end // case: STATE2
	   
           STATE3 : begin
              current_state <= `TQ STATE0;
           end // case: STATE3
	   
           default : current_state <= `TQ STATE0;
	 endcase // priority case (current_state)
      end // else: !if(reset)
   end // always_ff @

endmodule // testmod




