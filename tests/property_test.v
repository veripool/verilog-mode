
//////////////////////////////////////////////////////////////////////////////
//
//  Main
//
//////////////////////////////////////////////////////////////////////////////


module test();

   integer                    count;
   bit                        test_clk;
   
   
   // Create a test clock
   always #01.8 test_clk = ~test_clk;
   
   //**********************************************************************
   // Testing.
   // Shift a moving set of ones up the input vector. At each shift
   // the outputs should change, which is checked by the assertions
   // below. This test doesnt care which output changes, as that was
   // checked to be accurate by formal means.
   //**********************************************************************
   
   initial begin
      count=0;
   end
   
   always @(posedge test_clk) begin
      count++;
   end
   
   //**********************************************************************
   // SV assertions
   //**********************************************************************
   property p_lane_output_change_on_input_change;
      @(negedge test_clk)
        disable iff (ana_byp == 0)
          !$stable(lane_inputs) |-> !$stable(lane_outputs);
   endproperty
   
   a_lane_output_change_on_input_change: assert property (p_lane_output_change_on_input_change)
     else begin
        $error("ERROR! Analog Bypass: Input change not observed on the outputs: %h (lane)",
               lane_inputs);
     end // UNMATCHED !!
   endproperty //FIXME

   property p_sup_output_change_on_input_change;
      @(negedge test_clk)
        disable iff (ana_byp == 0)
          !$stable(sup_inputs) |-> !$stable(sup_outputs);
   endproperty
   
   a_sup_output_change_on_input_change: assert property (p_sup_output_change_on_input_change)
     else begin
        $error("ERROR! Analog Bypass: Input change not observed on the outputs: %h (sup)",
               sup_inputs);
     end
endproperty
endmodule // test
