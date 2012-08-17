interface ExampIf
  ( input logic clk );
   clocking mon_clkblk @(posedge clk);
      input 		req_val;
      input 		req_dat;
   endclocking
   modport mp(clocking mon_clkblk);
endinterface

module ExampMain
( input clk,
  /*AUTOINOUTMODPORT("ExampIf" "mp")*/
);

   /*AUTOASSIGNMODPORT("ExampIf" "mp" "inst")*/

endmodule
