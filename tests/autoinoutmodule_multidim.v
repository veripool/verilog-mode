module my_dut(
   input clk,
   input [3:0][7:0] data_in,
   output [3:0][7:0] data_out);
endmodule
 
module shell(
   /*AUTOINOUTMODULE("my_dut","","^input")*/
   );
endmodule
