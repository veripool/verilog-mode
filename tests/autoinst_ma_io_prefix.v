// From: "Ma, Zhenqiang" <Zhenqiang.Ma@caviumnetworks.com>

module test (
   // Ports for module A
   input  i_A_outsidei,
   output o_A_outsideo,

   // Ports for module B
   input  i_B_outsidei,
   output o_B_outsideo );

  /*AUTOWIRE*/

   //-----------------------------------------------------------------------------
   // instantiate module A
   //-----------------------------------------------------------------------------
   
   /* moduleA AUTO_TEMPLATE (
    .[iot]_\(.*\)        (@"(vl-prefix-i-o \\"\1\\")"\1[]),
   ); */

   moduleA u0(
     /*AUTOINST*/);


  //-----------------------------------------------------------------------------
  // instantiate module B
  //-----------------------------------------------------------------------------
  
  /* moduleB AUTO_TEMPLATE (
    .[iot]_\(.*\)        (@"(vl-prefix-i-o vl-dir)"\1[]),
  ); */

  moduleB u1(
       /*AUTOINST*/);


endmodule

module moduleA (
    input  i_A_outsidei,
    output o_A_outsideo,

    input  i_B_internal,
    output o_A_internal
  );
  /*AUTOTIEOFF*/
endmodule

module moduleB (
    input  i_B_outsidei,
    output o_B_outsideo,

    input  i_A_internal,
    output o_B_internal
  );
  /*AUTOTIEOFF*/
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
