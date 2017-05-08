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
   // Only blocking assignments
   initial begin
      lorem = 0;
      ip = 1;
      sum = 2;
   end
   // Only non-blocking assignments
   initial begin
      dolor <= 0;
      sit <= 1;
      amet <= 2;
   end
   // Mix of blocking and non-blocking assignments
   initial begin
      consectetur = 0;
      adipiscing <= 1;
      elit <= 2;
   end

endmodule

// Local Variables:
// verilog-auto-lineup: all
// End:

