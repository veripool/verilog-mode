module top
  #(parameter COLS = 4
    )
   ( input logic clk,
     input logic                 rstb,
     input logic [COLS-1:0]      ival,
     input logic [COLS-1:0][1:0] idata_some_extra_sig_length,
     output logic                reg_assigned
     );
   
   // Request: AUTOLOGIC instead of AUTOWIRE
   // Request: AUTOLOGIC would substitute all 3 existing macros AUTOWIRE/AUTOREG/AUTOREGINPUT, one would use AUTOLOGIC instead of AUTOWIRE/AUTOREG or AUTOWIRE/AUTOREGINPUT.
   
   // Could use AU-TOLOGIC
   // Or        AU-TOWIRE(logic)
   // And-or (setq verilog-auto-sv t)
   // And-or (setq verilog-auto-wire-type 'logic')
   
   /*AUTOOUTPUTEVERY*/
   // Beginning of automatic outputs (every signal)
   output logic       COLS;
   output logic       in1a; // To isub2 of sub2.v, ...
   output logic       in1b; // To isub1 of sub1.v
   output logic       in2b; // To isub2 of sub2.v
   output logic       out1a; // From isub1 of sub1.v
   output logic [1:0] out1b; // From isub1 of sub1.v
   output logic [1:0] out2b; // From isub2 of sub2.v
   // End of automatics
   
   /*AUTOREG*/
   
   /*AUTOREGINPUT*/
   // Beginning of automatic reg inputs (for undeclared instantiated-module inputs)
   logic              in1a; // To isub2 of sub2.v, ...
   logic              in1b; // To isub1 of sub1.v
   logic              in2b; // To isub2 of sub2.v
   // End of automatics
   
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic              out1a; // From isub1 of sub1.v
   logic [1:0]        out1b; // From isub1 of sub1.v
   logic [1:0]        out2b;                    // From isub2 of sub2.v
   // End of automatics
   
   /* sub2 AUTO_TEMPLATE(
    .idata_some_extra_sig_length ( s1_odata),
    .ival ( s1_oval),
    );*/
   sub2 isub2 (/*AUTOINST*/
               // Outputs
               .out2b                   (out2b[1:0]),
               // Inputs
               .in1a                    (in1a),
               .in2b                    (in2b),
               .out1a                   (out1a));
   
   
   sub1 isub1(/*AUTOINST*/
              // Outputs
              .out1a                    (out1a),
              .out1b                    (out1b[1:0]),
              // Inputs
              .in1a                     (in1a),
              .in1b                     (in1b));
   
   always @(posedge clk) begin
      reg_assigned <= 1;
   end
   
endmodule

module sub1
  ( input logic in1a,
    input logic        in1b,
    output logic       out1a,
    output logic [1:0] out1b
    );
endmodule

module sub2
  ( input logic in1a,
    input logic        in2b,
    input logic        out1a,
    output logic [1:0] out2b
    );
endmodule

// Local Variables:
// verilog-auto-wire-type: "logic"
// End:
