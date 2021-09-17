// From: "Ma, Zhenqiang" <Zhenqiang.Ma@caviumnetworks.com>

module test (
             // Ports for module A
             input  i_A_outsidei,
             output o_A_outsideo,
             
             // Ports for module B
             input  i_B_outsidei,
             output o_B_outsideo );
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire A_internal; // From u0 of moduleA.v
   wire A_outsideo; // From u0 of moduleA.v
   wire o_B_internal;           // From u1 of moduleB.v
   // End of automatics
   
   //-----------------------------------------------------------------------------
   // instantiate module A
   //-----------------------------------------------------------------------------
   
   /* moduleA AUTO_TEMPLATE (
    .[iot]_\(.*\)        (@"(vl-prefix-i-o \\"\1\\")"\1[]),
    ); */
   
   moduleA u0(
              /*AUTOINST*/
              // Outputs
              .o_A_outsideo             (A_outsideo),            // Templated
              .o_A_internal             (A_internal),            // Templated
              // Inputs
              .i_A_outsidei             (A_outsidei),            // Templated
              .i_B_internal             (B_internal));           // Templated
   
   
   //-----------------------------------------------------------------------------
   // instantiate module B
   //-----------------------------------------------------------------------------
   
   /* moduleB AUTO_TEMPLATE (
    .[iot]_\(.*\)        (@"(vl-prefix-i-o vl-dir)"\1[]),
    ); */
   
   moduleB u1(
              /*AUTOINST*/
              // Outputs
              .o_B_outsideo             (o_B_outsideo),          // Templated
              .o_B_internal             (o_B_internal),          // Templated
              // Inputs
              .i_B_outsidei             (i_B_outsidei),          // Templated
              .i_A_internal             (i_A_internal));                 // Templated
   
   
endmodule

module moduleA (
                input  i_A_outsidei,
                output o_A_outsideo,
                
                input  i_B_internal,
                output o_A_internal
                );
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   wire o_A_internal = 1'h0;
   wire o_A_outsideo = 1'h0;
   // End of automatics
endmodule

module moduleB (
                input  i_B_outsidei,
                output o_B_outsideo,
                
                input  i_A_internal,
                output o_B_internal
                );
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   wire o_B_internal = 1'h0;
   wire o_B_outsideo = 1'h0;
   // End of automatics
endmodule

/*
 Local Variables:
 eval:
 (defun vl-prefix-i-o (dir)
 (cond ((equal dir "input")
 "i_")
 ((equal dir "output")
 "o_")
 ((equal dir "inout")
 "t_")
 (t "")))
 End:
 */
