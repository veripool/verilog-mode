module x;
   reg a;
   reg b;
   reg c;
   always @(/*AUTOSENSE*/) begin
      if ( rst ) begin
	 /*AUTORESET*/
      end
      else begin
	 if ( a <= b ) begin
	    c = a;
	 end
	 else begin
	    c = b;
	 end
      end
   end

   always @ (posedge a) begin
      if ( rst ) begin
	 /*AUTORESET*/
      end
      else if ( a <= b ) begin
	 c <= a;
      end
   end

endmodule
