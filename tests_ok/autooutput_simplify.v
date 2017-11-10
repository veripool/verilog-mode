// msg2404

module top
  (
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input logic [2*2:1] x                        // To inst of submod.v
   // End of automatics
   /*AUTOOUTPUT*/
   );
   
   /*AUTOLOGIC*/
   
   submod inst
     (/*AUTOINST*/
      // Inputs
      .x                                (x[2*2:1]));
   
endmodule

module submod
  (input [2*2:1] x);
endmodule

// Local Variables:
// verilog-auto-simplify-expressions: nil
// End:
