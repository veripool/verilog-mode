module foo();
   initial begin
      a;
   end
   
   always @(a) begin
      b;
   end
   task a (a);
      begin
	 a = f;
      end
   endtask // a
   
   
   property p_2;
      @(posedge clk) b |-> ##1 c;
   endproperty
   property p_1;
      @(posedge clk) a |-> b;
   endproperty
   
   initial d;
   
   ap_1 assert property (p_1);
   ap_2 assert property (p_2);
   
   property p_lane_output_change_on_input_change;
      @(negedge test_clk)
        disable iff (ana_byp == 0)
	  !$stable(lane_inputs) |-> !$stable(lane_outputs);
   endproperty
endmodule