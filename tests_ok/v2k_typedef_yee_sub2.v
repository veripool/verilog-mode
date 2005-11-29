
`include "v2k_typedef_yee_inc.v"
module v2k_typedef_yee_sub2
  (/*AUTOARG*/
   // Outputs
   sub2_out_pixel, ready,
   // Inputs
   sub2_in_pixel, cp, reset, sub1_to_sub2, sub1_to_sub2_and_top, pixel_ff
   );

   output pixel24_t sub2_out_pixel,
	  output logic_t   ready,
	  input  pixel24_t sub2_in_pixel,
	  input  logic_t   cp,
	  input  logic_t   reset,
	  input  logic_t   sub1_to_sub2,
	  input  logic_t   sub1_to_sub2_and_top

	  pixel24_t pixel_ff;
   ff_t      sub1_to_sub2_ff;


   always_ff @(posedge cp) begin
      pixel_ff <= sub2_in_pixel;
      sub1_to_sub2_ff <= sub1_to_sub2;
   end

   assign sub2_out_pixel = pixel_ff;
   assign ready = sub1_to_sub2_ff;

endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
