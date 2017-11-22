// bug1242
// A and B will swap. We don't have a choice or will break autoinst_clog2_bug522.v

module test_submodule #
  (
   parameter A_WL = 16,
   parameter B_WL = 16
   )
   (
    input logic                   aclk,
    input logic signed [A_WL-1:0] a_tdata,
    input logic                   a_tvalid,
    input logic signed [B_WL-1:0] b_tdata,
    input logic                   b_tvalid
    );
   
endmodule : test_submodule

module test_top #
  (
   parameter int A_WL = 16,
   parameter int B_WL = 32
   )
   (
    
    input logic                   aclk,
    
    input logic signed [A_WL-1:0] a_tdata,
    input logic                   a_tvalid,
    
    input logic signed [B_WL-1:0] b_tdata,
    input logic                   b_tvalid
    );
   
   /* test_submodule AUTO_TEMPLATE (
    .A_\(.*\)                           (B_\1),
    .B_\(.*\)                           (A_\1),
    .a_\(.*\)                           (b_\1[]),
    .b_\(.*\)                           (a_\1[]),
    ); */
   
   test_submodule
     #(/*AUTOINSTPARAM*/
       // Parameters
       .A_WL                            (B_WL),                  // Templated
       .B_WL                            (A_WL))                  // Templated
   test_submodule_inst
     (/*AUTOINST*/
      // Inputs
      .aclk                             (aclk),
      .a_tdata                          (b_tdata[B_WL-1:0]),     // Templated
      .a_tvalid                 (b_tvalid),              // Templated
      .b_tdata                          (a_tdata[B_WL-1:0]),     // Templated
      .b_tvalid                 (a_tvalid));             // Templated
   
endmodule : test_top

// Local Variables:
// verilog-auto-inst-param-value:t
// End:
