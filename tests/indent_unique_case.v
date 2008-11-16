module foo;
   // syntaxify the unique keyword correctly please...
   always_comb (*) begin
      case (f)
	1 		  : 2;
      endcase // case (f)
      
      unique case(vlcnum)
	0 : unique case(in.value1)
		     0 	  : out = 1; 1 : out = 3; 2 : out = 3; 3 : out = 4;
		     4 	  : out = 4; 5 : out = 5; 6 : out = 5; 7 : out = 6;
		     8 	  : out = 6; 9 : out = 7; 10: out = 7; 11: out = 8;
		     12 	  : out = 8; 13: out = 9; 14: out = 9; 15: out = 9;
		   endcase
        1 	  :
	  unique
	  case(in.value1)
	    0 		  : out = 3;
	    1 	  : out = 3;
	    2 	  : out = 3;
	    3 	  : out = 3;
	    4 	  : out = 3;
	    5 	  : out = 4;
	    6 	  : out = 4;
	    7 	  : out = 4;
	    8 	  : out = 4;
	    9 	  : out = 5;
	    10   : out = 5;
	    11   : out = 6;
	    12   : out = 6;
	    13   : out = 6;
	    14   : out = 6;
	  endcase // case (in.value1)
      endcase // case (in.value1)
   end
endmodule
