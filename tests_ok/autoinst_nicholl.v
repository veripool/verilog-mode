module sub1 (/*AUTOARG*/
             // Inputs
             bus1
             );
   
   input [0:3] bus1;
   
endmodule

module sub2 (/*AUTOARG*/
             // Inputs
             bus2
             );
   
   input [0:3] bus2;
   
endmodule

module sub3 (/*AUTOARG*/
             // Outputs
             bus1, bus2
             );
   
   output [0:3] bus1;
   output [4:7] bus2;
   
endmodule


module top (/*AUTOARG*/);
   
   wire [4:7] bus2; // From sub3 of sub3.v
   
   /*AUTOINPUT*/
   /*AUTOOUTPUT*/
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [0:3] bus1;                     // From sub3 of sub3.v
   // End of automatics
   
   sub1 sub1 (/*AUTOINST*/
              // Inputs
              .bus1                     (bus1[0:3]));
   
   sub2 sub2 (/*AUTOINST*/
              // Inputs
              .bus2                     (bus2[0:3]));
   
   sub3 sub3 (/*AUTOINST*/
              // Outputs
              .bus1                     (bus1[0:3]),
              .bus2                     (bus2));
   
endmodule

// Local Variables:
// verilog-auto-inst-vector:nil
// End:
