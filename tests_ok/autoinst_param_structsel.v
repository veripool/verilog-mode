typedef struct packed {
   logic size;
} config_t;

parameter config_t CFG8 = '{size: 8};
parameter config_t CFG4 = '{size: 4};

module m0 (
           /*AUTOINPUT*/
           // Beginning of automatic inputs (from unused autoinst inputs)
           input                 a4, // To m4 of m4.v
           input                 a8, // To m8 of m8.v
           input [CFG.size-1:0]  b4, // To m4 of m4.v
           input [CFG8.size-1:0] b8  // To m8 of m8.v
           // End of automatics
           );
   m4
     m4(/*AUTOINST*/
        // Inputs
        .a4                             (a4),
        .b4                             (b4[CFG.size-1:0]));
   m8 #(.CFG(CFG8))
   m8(/*AUTOINST*/
      // Inputs
      .a8                               (a8),
      .b8                               (b8[CFG8.size-1:0]));
endmodule

module m4
  #(
    parameter config_t CFG = CFG4
    )
   (
    input                a4,
    input [CFG.size-1:0] b4
    );
endmodule

module m8
  #(
    parameter config_t CFG = CFG8
    )
   (
    input                a8,
    input [CFG.size-1:0] b8
    );
endmodule

// Local Variables:
// verilog-typedef-regexp: "_[tT]$"
// verilog-auto-inst-param-value:t
// verilog-auto-inst-param-value-type:t
// verilog-align-typedef-regexp: "\\<[a-zA-Z_][a-zA-Z_0-9]*_[tT]\\>"
// End:
