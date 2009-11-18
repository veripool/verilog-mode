// See forum topic 176
module autolisp_include (/*AUTOARG*/
   // Outputs
   foo,
   // Inputs
   bar
   );

   //`include "autolisp_include_inc.vh"
   /*AUTOINSERTLISP(verilog-library-filenames (insert-file "autolisp_include_inc.vh"))*/
   // Beginning of automatic insert lisp
  input bar;
  output foo;
   // End of automatics

   assign foo = bar;

   // This doesn't need commentary
   /*AUTOINSERTLISP(when nil)*/

endmodule
