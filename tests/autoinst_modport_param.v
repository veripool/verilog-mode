//bug565

module InstModule
  (svi.master svi_modport,
   input      clk,
   svi        svi_nomodport);
endmodule

module InstModule1 #
  (parameter TCQ = 100)
  (svi.master svi_modport,
   input      clk,
   svi        svi_nomodport);
endmodule

module top;
   InstModule instName
     (/*AUTOINST*/
      // Interfaces
      .svi_modport			(svi_modport.master),
      .svi_nomodport			(svi_nomodport),
      // Inputs
      .clk				(clk));

    InstModule1 instName1
     (/*AUTOINST*/
      // Interfaces
      .svi_modport			(svi_modport.master),
      .svi_nomodport			(svi_nomodport),
      // Inputs
      .clk				(clk));
  
endmodule

// Local Variables:
// verilog-library-directories:(".")
// verilog-library-extensions:(".v" ".sv")
// End:
