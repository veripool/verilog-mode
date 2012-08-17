interface ExampIf
  ( input logic clk );
   clocking mon_clkblk @(posedge clk);
      input req_val;
      input req_dat;
   endclocking
   modport mp(clocking mon_clkblk);
endinterface

module ExampMain
  ( input clk,
    /*AUTOINOUTMODPORT("ExampIf" "mp")*/
    // Beginning of automatic in/out/inouts (from modport)
    input req_dat,
    input req_val
    // End of automatics
    );
   
   /*AUTOASSIGNMODPORT("ExampIf" "mp" "inst")*/
   // Beginning of automatic assignments from modport
   assign inst.req_dat  = req_dat;
   assign inst.req_val  = req_val;
   // End of automatics
   
endmodule
