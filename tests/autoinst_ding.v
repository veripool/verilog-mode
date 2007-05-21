module AA(
	  /*AUTOINPUT*/
	  /*AUTOOUTPUT*/
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

module BB(
	  /*AUTOINPUT*/
	  /*AUTOOUTPUT*/
    input wire clock,
    input wire reset,
    input wire test_enable,
    input wire core_code_idle,
    input wire core_code_error,
    input wire [7:0] core_data,
    input wire [8:0] mbist_done,
    input wire [8:0] mbist_fail,
    output wire mbist_rst,
    output reg mbist_test
);
endmodule

module TOP(
	   /*AUTOINPUT*/
	   /*AUTOOUTPUT*/
	   );

AA AA_U(/*AUTOINST*/);

BB BB_U(/*AUTOINST*/);

// Local Variables:
// verilog-library-directories:(".")
// End:

endmodule
