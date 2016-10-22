`define XYZ            4'ha

module test ();

   always @(/*AUTOSENSE*/r or x)
     begin
	casex(x)
	  5: d = {r, `XYZ };
	endcase
     end

endmodule // test

// Local Variables:
// verilog-auto-read-includes:t
// End:
