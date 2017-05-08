module test1 ( wireA, wireB );
   output [3:0]  wireA;
   output [16:0] wireB;
endmodule

module test_top;
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]  wireA; // From t1 of test1.v
   wire [16:0] wireB;                   // From t1 of test1.v
   // End of automatics
   
   generate
      if (1) begin
         test1 t1 (/*AUTOINST*/
                   // Outputs
                   .wireA               (wireA[3:0]),
                   .wireB               (wireB[16:0]));
      end
      else begin
         assign wireA = 0;
      end
   endgenerate
endmodule
