module autoinst_sv_shaw
  (
   /*AUTOINOUTMODULE("Example_mod")*/
   // Beginning of automatic in/out/inouts (from specific module)
   input logic clk,
   input logic reset_b
   // End of automatics
   );
   
   Example_mod Ex1 (/*AUTOINST*/
                    // Inputs
                    .clk                (clk),
                    .reset_b            (reset_b));
   
endmodule

module Example_mod
  (
   input logic clk,
   input logic reset_b,
   );
endmodule

