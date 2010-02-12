module fork_join_any;
   initial begin
      fork
         begin
            fork
               begin
               end
            join_any
            a  = b;
            disable fork;
         end
      join_any
      foo  = bar;
   end // initial fork
endmodule // fork_join_any

class x;
   task y;
      a  = b;
      fork wait;
      $display("I'm indented too far");
   endtask // y
endclass // x

