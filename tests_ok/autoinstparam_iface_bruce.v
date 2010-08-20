module top;
   /*AUTOWIRE*/
   sub0 #(/*AUTOINSTPARAM*/
          // Parameters
          .testit2                      (testit2),
          .TESTIT                       (TESTIT))
   s0 (/*AUTOINST*/
       // Inputs
       .side_clk                        (side_clk),
       .side_rst_b                      (side_rst_b));
endmodule

module sub0
  #(
    parameter string testit2 = 0,
    int              TESTIT = 0
    ) (
       // clk and resets
       input logic side_clk,
       input logic side_rst_b,
       );
   
endmodule
