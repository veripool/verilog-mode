module top;
   
   /*AUTOOUTPUTEVERY*/
   // Beginning of automatic outputs (every signal)
   output logic       out1a;
   output logic [1:0] out1b;
   // End of automatics
   /*AUTOREG*/
   
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic              out1a;
   logic [1:0]        out1b;
   // End of automatics
   
   
   sub2 isub2 (/*AUTOINST*/
               // Outputs
               .out1a                   (out1a),
               .out1b                   (out1b[1:0]),
               // Inputs
               .in1a                    (in1a),
               .in1b                    (in1b));
   
endmodule

module sub2
  ( input logic in1a,
    input logic        in1b,
    output logic       out1a,
    output logic [1:0] out1b
    );
endmodule

// Local Variables:
// verilog-auto-wire-comment: nil
// End:
