module ExampInsertLisp;
   
   /*AUTOINSERTLISP(my-verilog-insert-hello "world")*/
   // Beginning of automatic insert lisp
   initial $write("hello world");
   // End of automatics
   
   // Try an empty insert
   /*AUTOINSERTLISP(+ 1)*/
   
   // Try a shell command
   /*AUTOINSERTLISP(insert (shell-command-to-string "echo //hello"))*/
   // Beginning of automatic insert lisp
   //hello
   // End of automatics
   
endmodule
/*
 Local Variables:
 eval:
 (defun my-verilog-insert-hello (who)
 (insert (concat "initial $write(\"hello " who "\");\n")))
 End:
 */
