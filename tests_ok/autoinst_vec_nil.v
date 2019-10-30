module sub
  (
   output signed [3:0] as,
   output [3:0]        bs);
endmodule

module t
  wire signed [3:0] as; // From sub of sub.v
   wire [3:0] bs;                       // From sub of sub.v
   
   sub sub (/*AUTOINST*/
            // Outputs
            .as                         (as),
            .bs                         (bs));
endmodule

// Local Variables:
// verilog-auto-inst-vector: nil
// End:
