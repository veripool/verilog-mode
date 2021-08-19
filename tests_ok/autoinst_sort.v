module unsort(
              input  t,
              input  a,
              input  z,
              
              output o,
              outp ut b);
endmodule

module t;
   unsort sub (/*AUTOINST*/
               // Outputs
               .b                       (b),
               .o                       (o),
               // Inputs
               .a                       (a),
               .t                       (t),
               .z                       (z));
endmodule

// Local Variables:
// verilog-auto-inst-sort: t
// End:
