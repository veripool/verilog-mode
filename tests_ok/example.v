module example (/*AUTOARG*/
   // Outputs
   lower_out, o,
   // Inputs
   lower_inb, lower_ina, i
   );
   input i;
   output o;
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		lower_ina;		// To inst of inst.v
   input		lower_inb;		// To inst of inst.v
   // End of automatics
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		lower_out;		// From inst of inst.v
   // End of automatics
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg			o;
   // End of automatics
   inst inst (/*AUTOINST*/
	      // Outputs
	      .lower_out		(lower_out),
	      // Inputs
	      .lower_inb		(lower_inb),
	      .lower_ina		(lower_ina));
   always @ (/*AUTOSENSE*/i) begin
      o = i;
   end
endmodule


