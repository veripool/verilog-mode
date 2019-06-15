        module ExampInsertLisp;
           /*AUTOINSERTLISP(my-verilog-insert-hello "world")*/
           // Beginning of automatic insert lisp
initial $write("hello world");
           // End of automatics
        endmodule

        // For this example we declare the function in the
        // module's file itself.  Often you'd define it instead
        // in a site-start.el or init file.
        /*
         Local Variables:
         eval:
           (defun my-verilog-insert-hello (who)
             (insert (concat "initial $write(\"hello " who "\");\n")))
         End:
        */
