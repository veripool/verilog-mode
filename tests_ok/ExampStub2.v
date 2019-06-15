module ExampMain
  (input unused_input_a, input unused_input_b);
endmodule

module ExampStub2 (/*AUTOARG*/
                   // Inputs
                   unused_input_a, unused_input_b
                   );
   /*AUTOINOUTPARAM("ExampMain")*/
   /*AUTOINOUTMODULE("ExampMain")*/
   // Beginning of automatic in/out/inouts (from specific module)
   input unused_input_a;
   input unused_input_b;
   // End of automatics
   
   /*AUTOTIEOFF*/
   
   // verilator lint_off UNUSED
   wire  _unused_ok = &{1'b0,
                        /*AUTOUNUSED*/
                        // Beginning of automatic unused inputs
                        unused_input_a,
                        unused_input_b,
                        // End of automatics
                        1'b0};
   // verilator lint_on  UNUSED
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
