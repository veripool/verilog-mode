module ex;

   /* subwidth AUTO_TEMPLATE (
    .bus1a(@"vl-width"'b0),
    .bus1b(@"vl-width"'b0),
    .bus4a(@"vl-width"'b0),
    .bus4b(@"vl-width"'b0),
    .busdef(@"vl-width"'b0),
    );*/

   subwidth u_a2(/*AUTOINST*/
		 // Outputs
		 .bus4a			(4'b0),			 // Templated
		 .bus4b			(4'b0),			 // Templated
		 .bus1a			(1'b0),			 // Templated
		 .bus1b			(1'b0),			 // Templated
		 .busdef		((1+(`defa)-(`defb))'b0)); // Templated

endmodule

module subwidth (/*AUTOARG*/
   // Outputs
   bus4a, bus4b, bus1a, bus1b, busdef
   );

   output [0:3] bus4a;
   output [7:4] bus4b;
   output       bus1a;
   output [0:0] bus1b;
   output [`defa:`defb] busdef;

endmodule
