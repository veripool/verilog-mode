// bug 895 - labeling of always constructs
module example;
   
   always
     begin
     end // always
   
   always @(posedge clk)
     begin
     end // always @ (posedge clk)
   
   always @*
     begin
     end // always @ *
   
   always @(*)
     begin
     end // always @ (*)
   
   always_comb
     begin
     end // always_comb
   
   always_latch
     begin
     end // always_latch
   
   always @( *)
     begin
     end // always @ ( *)
   
   always @(* )
     begin
     end // always @ (* )
   
   always_ff @(posedge clk)
     begin
     end // always_ff @ (posedge clk)
   
   always @(*)
     begin
     end // always @ (*)
   
endmodule // example

// Local Variables:
// verilog-minimum-comment-distance: 1
// verilog-auto-endcomments: t
// End:
