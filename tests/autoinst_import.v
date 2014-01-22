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
     (/*AUTOINST*/);

    InstModule1 instName1
     (/*AUTOINST*/);

endmodule

// Local Variables:
// verilog-library-directories:(".")
// verilog-library-extensions:(".v" ".sv")
// End:
