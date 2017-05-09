module assert_test;
   reg [31:0] whatever2;
   initial begin
      a = b;
      assert(std::randomize(whatever2)  with { whatever2   inside {[10:100]};});
   end
endmodule // assert_test
