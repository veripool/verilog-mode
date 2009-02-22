module foo (/*AUTOARG*/
            // Outputs
            d,
            // Inputs
            b, a
            );
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input  a; // To foo2 of foo2.v
   input  b; // To foo2 of foo2.v
   // End of automatics
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output d;                    // From foo2 of foo2.v
   // End of automatics
   /*AUTOWIRE*/
   /*AUTOREGINPUT*/
   foo2 foo2 (/*AUTOINST*/
              // Outputs
              .d                        (d),
              // Inputs
              .a                        (a),
              .b                        (b));
   
endmodule


module foo2 (/*AUTOARG*/
             // Outputs
             d,
             // Inputs
             a, b
             );
   /*AUTOINPUT*/
   /*AUTOOUTPUT*/
   /*AUTOWIRE*/
   /*AUTOREGINPUT*/
   input  a;
   input  b;
   output d;
   
   //{ Behavioral verilog code here}
endmodule

