module x;

   input [5:0] state;
   output [5:0] next;

   parameter 	CYCLEA = 1;
   parameter 	CYCLEC = 2;
   parameter 	MSTRA = 3;
   parameter 	MSTRB = 4;
   parameter 	MSTRC = 5;

   // make sure 'state' is listed
   always @ (/*AUTOSENSE*/done or nREQA or nREQB or nREQC or state) begin
      next = 6'b0;
      case (1'b1)
        state[CYCLEC] : begin
	   if (!nREQA && done)                         next[MSTRA] = 1'b1;
	   else if (!nREQB && nREQA && done)next[MSTRB] = 1'b1;
	   else if (!nREQC && nREQA && nREQB && done) next[MSTRC] = 1'b1;
	   else next[CYCLEC] = 1'b1;
	end
        state[MSTRA] : begin
	   if (!nREQB || !nREQC) next[CYCLEA] = 1'b1;
	   else                           next[MSTRA] = 1'b1;
	end
      endcase
   end
endmodule
