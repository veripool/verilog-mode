module xyz (/*AUTOARG*/
            // Inputs
            signal_e3, signal_e, signal_b
            );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [2:0] signal_b; // To u_abc of abc.v
   input       signal_e; // To u_def of def.v
   input       signal_e3; // To u_def of def.v
   // End of automatics
   
   /*AUTOOUTPUT*/
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire        signal_c; // From u_abc of abc.v
   wire        signal_f;                // From u_def of def.v
   // End of automatics
   
   /* abc AUTO_TEMPLATE
    (
    // Outputs
    .signal_c                           (signal_c),
    // Inputs
    .signal_a                           ({1'b0, signal_f}),
    .signal_b                           (signal_b[2:0]));
    */
   
   abc u_abc
     (/*AUTOINST*/
      // Outputs
      .signal_c                         (signal_c),              // Templated
      // Inputs
      .signal_a                         ({1'b0, signal_f}),      // Templated
      .signal_b                         (signal_b[2:0]));        // Templated
   
   /* def AUTO_TEMPLATE
    (// Outputs
    .signal_f                           (signal_f),
    // Inputs
    .signal_d                           ({1'b1, signal_c}),
    .signal_e                           ({2'b11, signal_e}),
    .signal_e2                  (({2'b11, signal_e2})),
    .signal_e3                  ((signal_e3)) );
    */
   
   def u_def
     (/*AUTOINST*/
      // Outputs
      .signal_f                         (signal_f),              // Templated
      // Inputs
      .signal_d                         ({1'b1, signal_c}),      // Templated
      .signal_e                         ({2'b11, signal_e}),     // Templated
      .signal_e2                        (({2'b11, signal_e2})),  // Templated
      .signal_e3                        ((signal_e3)));          // Templated
   
endmodule // xyz

module abc (/*AUTOARG*/
            // Outputs
            signal_c,
            // Inputs
            signal_a, signal_b
            );
   
   input [1:0] signal_a;
   input [2:0] signal_b;
   output      signal_c;
   
endmodule // abc

module def (/*AUTOARG*/
            // Outputs
            signal_f,
            // Inputs
            signal_d, signal_e, signal_e2, signal_e3
            );
   
   input [1:0] signal_d;
   input [2:0] signal_e;
   input [3:0] signal_e2;
   input [3:0] signal_e3;
   output      signal_f;
   
endmodule // def

// Local Variables:
// verilog-auto-ignore-concat: t
// End:
