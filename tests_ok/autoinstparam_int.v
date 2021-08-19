module xyz
  #(parameter int FOO=1, BAR=2,
    parameter logic [5:0] BLUP=3, ZOT=4,
    parameter             LDWRDS=5)
   ( input x1, x2,
     input int         i1, i2,
     input logic [5:0] i3, i4,
     input             i5,
     output            y);
endmodule

module pdq;
   input         x; output y;
   parameter int FOO=1;
endmodule

module abc;
   xyz XYZ
     #(/*AUTOINSTPARAM*/
       // Parameters
       .FOO                             (FOO),
       .BAR                             (BAR),
       .BLUP                            (BLUP[5:0]),
       .ZOT                             (ZOT[5:0]),
       .LDWRDS                          (LDWRDS))
   (/*AUTOINST*/
    // Outputs
    .y                                  (y),
    // Inputs
    .x1                                 (x1),
    .x2                                 (x2),
    .i1                                 (i1),
    .i2                                 (i2),
    .i3                                 (i3[5:0]),
    .i4                                 (i4[5:0]),
    .i5                                 (i5));
   pdq PDQ
     #(/*AUTOINSTPARAM*/
       // Parameters
       .FOO                             (FOO))
   (/*AUTOINST*/
    // Outputs
    .y                                  (y),
    // Inputs
    .x                                  (x));
endmodule
