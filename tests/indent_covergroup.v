module coverage;
   enum { red, green, blue } color;
   covergroup foo @(posedge clk);
      c : coverpoint color;
      c : coverpoint color;
      c : coverpoint color;
      c : coverpoint color;      
   endgroup // foo
   
   foo 	  = bar;
   
   sequence bar
     b 	  = c;
   endsequence // bar
   j 	  = taskt;
   function foo;
      begin
	 foo 	= 1;
      end
   endfunction // foo
   
   randsequence bar
     b 		= c;
   endsequence // bar
   
   case (foo)
     1: a;
     2:b;
   endcase // case (foo)
   
   casex (foo)
     1: a;
     2:b;
   endcase // case (foo)
   
   casez (foo)
     1: a;
     2:b;
   endcase // case (foo)
   
   randcase (foo)
     1: a;
     2:b;
   endcase // case (foo)
   
endmodule // coverage
