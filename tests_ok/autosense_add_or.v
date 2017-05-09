module autosense_or(/*AUTOARG*/
                    // Outputs
                    x, y,
                    // Inputs
                    a, c
                    );
   
   input  a;
   input  c;
   output x;
   output y;
   
   always @(a/*AUTOSENSE*/) begin
      x = a;
   end
   always @(a/*AUTOSENSE*/ or c) begin
      x = a | c;
   end
   //   always @(a or/*AUTOSENSE*/c) begin
   //      x = a | c;
   //   end
   
endmodule

