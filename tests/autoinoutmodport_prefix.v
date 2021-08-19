interface ExampIf
  ( input logic clk );
   logic        req_val;
   logic [7:0]  req_dat;
   logic        out;
   clocking mon_clkblk @(posedge clk);
      input     req_val;
      input     req_dat;
      output	out;
   endclocking
   modport mp(clocking mon_clkblk);
endinterface


module ExampMain
( input clk,

  // Manually declared, so make sure not redeclared
  // Note this is AFTER addition of the prefix
  input a_req_dat,

  /*AUTOINOUTMODPORT("ExampIf", "mp", "", "a_")*/
  /*AUTOINOUTMODPORT("ExampIf", "mp", "", "b_")*/
);

   ExampleIf ia;
   ExampleIf ib;

   // Manually declared (duplications are NOT detected yet)
   assign a_out = 1;

   /*AUTOASSIGNMODPORT("ExampIf", "mp", "ia", "", "a_")*/
   /*AUTOASSIGNMODPORT("ExampIf", "mp", "ib", "", "b_")*/

endmodule
