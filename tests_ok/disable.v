module foo;
   task my_task;
      begin :body_my_task
         fork
         join
         case (a)
         endcase // case endcase
         if (a) begin
         end
         begin
         end
         fork : main_fork
            begin : body_main_fork
               fork : sub_fork
                  begin
                     // st1
                  end
                  begin
                     // st2
                  end
               join_any // first wins
               a = b;
               disable fork; // kill others
            end // block: body_main_fork
         end // block: body_main_fork
   endtask // my_task
endmodule // foo
