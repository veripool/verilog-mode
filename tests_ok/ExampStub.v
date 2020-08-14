module ExampMain
  #(parameter P)
   (input i, output o, inout io);
endmodule

module ExampStub (/*AUTOARG*/
                  // Outputs
                  o,
                  // Inouts
                  io,
                  // Inputs
                  i
                  );
   /*AUTOINOUTPARAM("ExampMain")*/
   // Beginning of automatic parameters (from specific module)
   parameter P;
   // End of automatics
   /*AUTOINOUTMODULE("ExampMain")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output    o;
   inout     io;
   input     i;
   // End of automatics
   
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   wire      o = 1'h0;
   // End of automatics
   
   // verilator lint_off UNUSED
   wire      _unused_ok = &{1'b0,
                            /*AUTOUNUSED*/
                            // Beginning of automatic unused inputs
                            i,
                            io,
                            // End of automatics
                            1'b0};
   // verilator lint_on  UNUSED
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
