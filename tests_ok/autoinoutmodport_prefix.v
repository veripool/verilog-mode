interface ExampIf
  ( input logic clk );
   logic       req_val;
   logic [7:0] req_dat;
   logic       out;
   clocking mon_clkblk @(posedge clk);
      input  req_val;
      input  req_dat;
      output out;
   endclocking
   modport mp(clocking mon_clkblk);
endinterface


module ExampMain
  ( input clk,
    
    // Manually declared, so make sure not redeclared
    // Note this is AFTER addition of the prefix
    input       a_req_dat,
    
    /*AUTOINOUTMODPORT("ExampIf", "mp", "", "a_")*/
    // Beginning of automatic in/out/inouts (from modport)
    output      a_out,
    input       a_req_val,
    // End of automatics
    /*AUTOINOUTMODPORT("ExampIf", "mp", "", "b_")*/
    // Beginning of automatic in/out/inouts (from modport)
    output      b_out,
    input       b_req_val,
    input [7:0] b_req_dat
    // End of automatics
    );
   
   ExampleIf ia;
   ExampleIf ib;
   
   // Manually declared (duplications are NOT detected yet)
   assign a_out = 1;
   
   /*AUTOASSIGNMODPORT("ExampIf", "mp", "ia", "", "a_")*/
   // Beginning of automatic assignments from modport
   assign a_out = ia.out;
   assign ia.req_dat = a_req_dat;
   assign ia.req_val = a_req_val;
   // End of automatics
   /*AUTOASSIGNMODPORT("ExampIf", "mp", "ib", "", "b_")*/
   // Beginning of automatic assignments from modport
   assign b_out = ib.out;
   assign ib.req_dat = b_req_dat;
   assign ib.req_val = b_req_val;
   // End of automatics
   
endmodule
