module autowire_topv;
   /*AUTOOUTPUT("bar")*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [1:0] bar; // From one of autowire_topv_one.v
   output [1:0] bar2; // From two of autowire_topv_two.v
   output       bar3; // From two of autowire_topv_two.v
   // End of automatics
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [1:0]   foo; // From one of autowire_topv_one.v
   wire [1:0]   foo2; // From two of autowire_topv_two.v
   wire         foo3;                   // From two of autowire_topv_two.v
   // End of automatics
   
   autowire_topv_one one (/*AUTOINST*/
                          // Outputs
                          .foo                  (foo[1:0]),
                          .bar                  (bar[1:0]));
   autowire_topv_two two (/*AUTOINST*/
                          // Outputs
                          .foo2                 (foo2[1:0]),
                          .foo3                 (foo3),
                          .bar2                 (bar2[1:0]),
                          .bar3                 (bar3));
endmodule

// Local Variables:
// verilog-auto-wire-type: "wire"
// End:
