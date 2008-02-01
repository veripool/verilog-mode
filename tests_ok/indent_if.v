module foo;
   initial
     if (cond1) begin
	sig1 <= {4'h0, 4'hc};
	sig2 <= 8'hff;
     end // if (cond1)
endmodule // foo
