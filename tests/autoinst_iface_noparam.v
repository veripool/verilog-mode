// bug1253

interface iface #(D  = 64) (input bit clk);
   logic clk;
endinterface: iface

module dut
    #(
      parameter D = 16,
      )
      (
       input logic clk,
       iface i_if_nopar,
       iface #(.D(D)) i_if_param1,
       iface #(.FOO(FOO), .BAR(BAR)) i_if_param2,
       iface i_if_nopar3
       );
   // Interface reference directly above ends up looking like noniface
   endmodule 

module tb_top;

      dut
	     #(/*AUTOINSTPARAM*/
	       // Parameters
	       .D			(D))
         dut
	         (/*AUTOINST*/
		  // Interfaces
		  .i_if_nopar		(i_if_nopar),
		  .i_if_param1		(i_if_param1),
		  .i_if_param2		(i_if_param2),
		  .i_if_nopar3		(i_if_nopar3),
		  // Inputs
		  .clk			(clk));
   endmodule 
