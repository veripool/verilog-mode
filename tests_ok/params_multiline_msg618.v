module testMultiLineParams (/*AUTOARG*/) ;
`include "params_multiline_msg618_inc.vh"
   reg                    comboIn, comboOut;
   
   // expect AUTOSENSE to be comboIn only, no params
   always @ ( /*AUTOSENSE*/comboIn) begin
      comboOout = param1 & param2 & param3 & comboIn;
   end
   
endmodule // foo

// Local Variables:
// verilog-library-directories:(".")
// verilog-auto-read-includes:t
// End:
