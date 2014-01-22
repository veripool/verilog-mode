//bug709

module InstModule
  (input      clk,
   svi.master svi_modport,
   svi        svi_nomodport);
endmodule // InstModule

module InstModule1 import mdp_pkg::*;
   (input      clk,
    svi.master svi_modport,
    svi        svi_nomodport);
endmodule

module top;
   InstModule instName
     (/*AUTOINST*/
      // Interfaces
      .svi_modport                      (svi_modport.master),
      .svi_nomodport                    (svi_nomodport),
      // Inputs
      .clk                              (clk));
   
   InstModule1 instName1
     (/*AUTOINST*/
      // Interfaces
      .svi_modport                      (svi_modport.master),
      .svi_nomodport                    (svi_nomodport),
      // Inputs
      .clk                              (clk));
   
endmodule

// Local Variables:
// verilog-library-directories:(".")
// verilog-library-extensions:(".v" ".sv")
// End:
