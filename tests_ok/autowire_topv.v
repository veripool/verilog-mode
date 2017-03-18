module autowire_topv;
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [1:0] foo; // From one of autowire_topv_one.v
   wire [1:0] foo2;                     // From two of autowire_topv_two.v
   // End of automatics
   autowire_topv_one one (/*AUTOINST*/
                          // Outputs
                          .foo                  (foo[1:0]));
   autowire_topv_two two (/*AUTOINST*/
                          // Outputs
                          .foo2                 (foo2[1:0]));
endmodule

// Local Variables:
// verilog-auto-wire-type: "wire"
// End:
