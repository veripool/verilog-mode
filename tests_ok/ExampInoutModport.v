interface ExampIf
  ( input logic clk );
   logic       req_val;
   logic [7:0] req_dat;
   clocking mon_clkblk @(posedge clk);
      input req_val;
      input req_dat;
   endclocking
   modport mp(clocking mon_clkblk);
endinterface

module ExampMain
  ( input clk,
    /*AUTOINOUTMODPORT("ExampIf", "mp")*/
    // Beginning of automatic in/out/inouts (from modport)
    input       req_val,
    input [7:0] req_dat
    // End of automatics
    );
   /*AUTOASSIGNMODPORT("ExampIf", "mp", "inst")*/
   // Beginning of automatic assignments from modport
   assign inst.req_dat = req_dat;
   assign inst.req_val = req_val;
   // End of automatics
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
