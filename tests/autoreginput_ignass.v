module autoreginput;

   /*AUTOREGINPUT*/
   // Beginning of automatic reg inputs (for undeclared instantiated-module inputs)
   reg			lower_ina;		// To inst of inst.v
   reg			lower_inb;		// To inst of inst.v
   // End of automatics
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire			lower_out;		// From inst of inst.v
   // End of automatics

   assign lower_ina = 1;

   inst inst (/*AUTOINST*/
	      // Outputs
	      .lower_out		(lower_out),
	      // Inputs
	      .lower_inb		(lower_inb),
	      .lower_ina		(lower_ina));

endmodule

// Local Variables:
// verilog-auto-reg-input-assigned-ignore-regexp: ".*"
// End:
