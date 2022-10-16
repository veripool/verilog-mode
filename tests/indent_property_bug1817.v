module test
  ();

`ifdef SVA
   property check_x;
   @(negedge clk_n) disable iff (!rst_n)
     ;
endproperty

   property check_y;
      @(negedge clk_n) disable iff (!rst_n)
        ;
   endproperty

`endif

endmodule
