module AA(
   input  wire clock,
   input  wire reset,
   input  wire test_enable,
   input  wire afe_ctrl,
   input  wire cpu_wr,
   input  wire [4:0] cpu_addr,
   input  wire [7:0] cpu_wdata,
   output wire [7:0] core_data,
   output wire core_code_error,
   output wire core_code_idle,
   output wire [7:0] cpu_rdata
);
endmodule

module TOP(
	   /*AUTOINPUT*/
	   /*AUTOOUTPUT*/
	   );

   genvar x;

AA AA_U(
	// Inputs
	.test_enable			(x),
	/*AUTOINST*/);

endmodule
