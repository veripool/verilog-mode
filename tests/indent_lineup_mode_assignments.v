module test (pci_ack, reg_wr, reg_sel, clk,  rst); 
   input [3:0] pci_ack; 
   input reg_wr;
   input reg_sel; 
   input clk; 
   input rst;
   initial begin
      foo;
      bar;
      x <= y;
      longish <= alsolongish;
   end

endmodule

// Local Variables:
// verilog-auto-lineup: assignments
// End:
