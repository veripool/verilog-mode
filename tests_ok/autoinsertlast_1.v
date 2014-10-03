module ExampInsertLisp;
   
   /*AUTOINSERTLAST(my-verilog-insert-hello "world")*/
   // Beginning of automatic insert lisp
   initial $write("hello world");
   // End of automatics
   
endmodule
/*
 Local Variables:
 eval:
 (defun my-verilog-insert-hello (who)
 (insert (concat "initial $write(\"hello " who "\");\n")))
 End:
 */
