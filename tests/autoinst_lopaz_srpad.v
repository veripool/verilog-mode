module autoinst_lopaz_srpad (/*AUTOARG*/
   // Outputs
   pin_in,
   // Inouts
   pin,
   // Inputs
   clk, pin_out, pin_outen
   );
   parameter w = 1;
   input     clk;

   inout [w-1:0] pin;
   output [2*w-1:0] pin_in;
   input [w-1:0]    pin_out;
   input 	    pin_outen;

endmodule
