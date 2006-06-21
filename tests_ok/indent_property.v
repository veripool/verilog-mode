module foo();
   initial begin
      a;
   end
   
   always @(a) begin
      b;
   end
   task t;
      c;
   endtask // t
   
   property p_1;
      @(posedge clk) a |-> b;
   endproperty
   initial
     d;
   
   property p_2;
      @(posedge clk) b |-> ##1 c;
   endproperty

   ap_1 assert property (p_1);
   ap_2 assert property (p_2);
   
endmodule