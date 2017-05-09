
`include "v2k_typedef_yee_inc.v"
module v2k_typedef_yee_sub1
  (
   output pixel24_t sub1_out_pixel,
   input  pixel24_t sub1_in_pixel,
   input  logic_t cp,
   input  logic_t reset,
   output logic_t sub1_to_sub2,
   output logic_t sub1_to_sub2_and_top
   );
   
   
   pixel24_t pixel_ff;
   
   
   always_ff @(posedge cp) begin
      pixel_ff <= sub1_in_pixel;
   end
   
   assign sub1_out_pixel = pixel_ff;
   assign sub1_to_sub2 = '1;
   assign sub1_to_sub2_and_top = '1;
   
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
