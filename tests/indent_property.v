module foo();
   initial begin
      a;
   end
   
   always @(a) begin
      b;
   end
   task a (a);
      begin
     a 	= f;
a      = f;
 d     <= 89;
 sdf    = sdf;
         adada  => asda;
 d     ->> g;
 aasd  <<<= 3;
                   	 ccc   %= 6;
d     *= b;
g     -= c;
      end
   endtask // a
   
   
   property p_3;
      a      => ##3 !a;        
      a     |=> ##1 !a;
      a     |-> ##2 !a;
   endproperty   
   property p_2;
      @(posedge clk) b |-> ##1 c;
   endproperty
   property p_1;
      @(posedge clk) a |-> b;
   endproperty
   
   initial d;
   
   //   ap_1 assert property (p_1);  FIXME
   //   ap_2 assert property (p_2);
   
   property p_lane_output_change_on_input_change;
      @(negedge test_clk)
        disable iff (ana_byp == 0)
          !$stable(lane_inputs) |-> !$stable(lane_outputs);
   endproperty

// Issue #940 - '=' in |=> , #=#, and [=n] operators should not mis-indent next line of continued expression
property p_nonSequential;
a |-> b[=n] ##0
c;
endproperty

property p_nonOverlapFollowedBy;
a #=#
c;
endproperty

property p_nonBlockingImplication;
a |=> b[*n] ##0
c;
endproperty


endmodule
