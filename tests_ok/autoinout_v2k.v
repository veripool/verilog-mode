module parent
  (
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [3:0] a2, // To sub_module of child_a.v
   input [3:0] a3, // To sub_module of child_a.v
   input       clk, // To sub_module of child_a.v, ...
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output      d, // From sub_module of child_a.v
   // End of automatics
   
   /*AUTOINOUT*/
   // Beginning of automatic inouts (from unused autoinst inouts)
   inout [5:0] c, // To/From sub_module of child_a.v, ...
   inout [5:0] c2, // To/From sub_module of child_a.v, ...
   inout       c3                       // To/From sub_module of child_a.v, ...
   // End of automatics
   );
   
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0] a; // From sub_module of child_b.v
   wire [3:0] a4; // From sub_module of child_b.v
   wire [2:0] b; // From sub_module of child_a.v
   wire [2:0] b2; // From sub_module of child_a.v
   wire [2:0] b3; // From sub_module of child_a.v
   wire [2:0] b4;                       // From sub_module of child_a.v
   // End of automatics
   
   
   child_a sub_module
     (/*AUTOINST*/
      // Outputs
      .b                                        (b[2:0]),
      .b2                               (b2[2:0]),
      .b3                               (b3[2:0]),
      .b4                               (b4[2:0]),
      .d                                        (d),
      // Inouts
      .c                                        (c[5:0]),
      .c2                               (c2[5:0]),
      .c3                               (c3),
      // Inputs
      .a                                        (a[3:0]),
      .a2                               (a2[3:0]),
      .a3                               (a3[3:0]),
      .a4                               (a4[3:0]),
      .clk                              (clk));
   
   child_b sub_module
     (/*AUTOINST*/
      // Outputs
      .a                                        (a[3:0]),
      .a4                               (a4[3:0]),
      // Inouts
      .c                                        (c[5:0]),
      .c2                               (c2[5:0]),
      .c3                               (c3),
      // Inputs
      .b                                        (b[2:0]),
      .b2                               (b2[2:0]),
      .b3                               (b3[2:0]),
      .b4                               (b4[2:0]),
      .clk                              (clk));
   
endmodule // parent

module child_a
  (
   input [3:0]  a,
   input [3:0]  a2,
   input [3:0]  a3,
   input [3:0]  a4,
   inout [5:0]  c,
   inout [5:0]  c2,
   inout        c3,
   output [2:0] b,
   output [2:0] b2,
   output [2:0] b3,
   output [2:0] b4,
   input        clk,
   output       d
   );
endmodule


module child_b
  (
   output [3:0] a,
   output [3:0] a4,
   inout [5:0]  c,
   inout [5:0]  c2,
   inout        c3,
   input [2:0]  b,
   input [2:0]  b2,
   input [2:0]  b3,
   input [2:0]  b4,
   input        clk
   );
endmodule
