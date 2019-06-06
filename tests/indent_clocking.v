module t;
   default clocking @(posedge clk);
      begin
	 a  = 8;
      end
   endclocking
   default clocking clocking_identifier;
      property foo (a)
	a   = b;
      endproperty
      cover property (prop) $display("**COVERAGE**");
      assert property (foo) a;
      assume property (bar) b;
      b1: assume property (bar) b;
	 B2: assert property (foo) a;
	    B2: cover property (foo) a;
	       assume property (bar) b;	       
	       a;
endmodule
