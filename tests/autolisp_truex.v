module ExampInsertLisp;

   /*AUTOINSERTLISP(my-verilog-insert-hello "world")*/

   // Try an empty insert
   /*AUTOINSERTLISP(+ 1)*/

   // Try a shell command
   /*AUTOINSERTLISP(insert (shell-command-to-string "echo //hello"))*/

endmodule
/*
 Local Variables:
 eval:
   (defun my-verilog-insert-hello (who)
     (insert (concat "initial $write(\"hello " who "\");\n")))
 End:
*/
