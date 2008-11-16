interface simple_bus; // Define the interface
 logic req, gnt;
   logic [7:0] addr, data;
   logic [1:0] mode;
   logic       start, rdy;
endinterface: simple_bus
module memMod(
	      simple_bus a, // Access the simple_bus interface
    input bit clk);
   
   logic  avail;
   // When memMod is instantiated in module top, a.req is the req
   // signal in the sb_intf instance of the simple_bus interface
   always @(posedge clk) 
     a.gnt <= a.req & avail;
endmodule
module cpuMod(simple_bus b, input bit clk);
   always @(b) begin
   end
endmodule
module top;
   logic clk = 0;
   simple_bus sb_intf(); // Instantiate the interface
   memMod mem(sb_intf, clk); // Connect the interface to the module instance
   cpuMod cpu(.b(sb_intf), .clk(clk)); // Either by position or by name
endmodule

