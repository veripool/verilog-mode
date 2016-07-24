module aa;

   int a,b,c;

   initial begin
      randcase
        10 : begin
           a = 1;
        end
	15 : begin
           b = 0;
           c = 5;
	end
      endcase // randcase

   end // initial begin

endmodule // a
