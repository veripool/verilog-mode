module io1_sub (/*AUTOARG*/);

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [w-1:0]		pin;			// To/From MD31_pad of autoinst_lopaz_srpad.v
   wire [2*w-1:0]	pin_in;			// From MD31_pad of autoinst_lopaz_srpad.v, ...
   wire			templated;		// To/From MD31_pad of autoinst_lopaz_srpad.v
   // End of automatics

   autoinst_lopaz_srpad MD31_pad
     (.*,
      .foo (touch_this_not_my_pretty));

   /* autoinst_lopaz_srpad AUTO_TEMPLATE (
    ); */

   autoinst_lopaz_srpad MD31_pad
     (.*);

   /* autoinst_lopaz_srpad AUTO_TEMPLATE (
    .pin	(templated));
    */

   autoinst_lopaz_srpad MD31_pad
     (.*,
      // Outputs
      // Inouts
      .pin				(templated)		 // Templated
      );

   // And .name with auto inst
   autoinst_lopaz_srpad MD31_pad22
     (.pin,
      .clk,
      /*AUTOINST*/
      // Outputs
      .pin_in				(pin_in[2*w-1:0]),
      // Inputs
      .pin_out				(pin_out[w-1:0]),
      .pin_outen			(pin_outen));

   always @(posedge clk) begin
      $display ("This .* shouldn't expand.\n");
   end

endmodule
