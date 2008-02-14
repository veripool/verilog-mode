module foo;
   initial
     begin
       s1;
     end

   always @(a)
     begin
	s1;
     end // always @ (a)
   always
     begin
	s1;
     end // always begin
   always_ff
     begin
     end // always_ff begin
   task
     t;
   endtask // t

endmodule // foo
