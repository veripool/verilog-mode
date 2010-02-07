module AA(
          /*AUTOINPUT*/
          /*AUTOOUTPUT*/
          input wire        clock,
          input wire        reset,
          input wire        test_enable,
          input wire        afe_ctrl,
          input wire        cpu_wr,
          input wire [4:0]  cpu_addr,
          input wire [7:0]  cpu_wdata,
          output wire [7:0] core_data,
          output wire       core_code_error,
          output wire       core_code_idle,
          output wire [7:0] cpu_rdata
          );
endmodule

module BB(
          /*AUTOINPUT*/
          /*AUTOOUTPUT*/
          input wire       clock,
          input wire       reset,
          input wire       test_enable,
          input wire       core_code_idle,
          input wire       core_code_error,
          input wire [7:0] core_data,
          input wire [8:0] mbist_done,
          input wire [8:0] mbist_fail,
          output wire      mbist_rst,
          output reg       mbist_test
          );
endmodule

module TOP(
           /*AUTOINPUT*/
           // Beginning of automatic inputs (from unused autoinst inputs)
           input        afe_ctrl, // To AA_U of AA.v
           input        clock, // To AA_U of AA.v, ...
           input [4:0]  cpu_addr, // To AA_U of AA.v
           input [7:0]  cpu_wdata, // To AA_U of AA.v
           input        cpu_wr, // To AA_U of AA.v
           input [8:0]  mbist_done, // To BB_U of BB.v
           input [8:0]  mbist_fail, // To BB_U of BB.v
           input        reset, // To AA_U of AA.v, ...
           input        test_enable, // To AA_U of AA.v, ...
           // End of automatics
           /*AUTOOUTPUT*/
           // Beginning of automatic outputs (from unused autoinst outputs)
           output [7:0] cpu_rdata, // From AA_U of AA.v
           output       mbist_rst, // From BB_U of BB.v
           output       mbist_test                 // From BB_U of BB.v
           // End of automatics
           );
   
   AA AA_U(/*AUTOINST*/
           // Outputs
           .core_data                   (core_data[7:0]),
           .core_code_error             (core_code_error),
           .core_code_idle                      (core_code_idle),
           .cpu_rdata                   (cpu_rdata[7:0]),
           // Inputs
           .clock                               (clock),
           .reset                               (reset),
           .test_enable                 (test_enable),
           .afe_ctrl                    (afe_ctrl),
           .cpu_wr                              (cpu_wr),
           .cpu_addr                    (cpu_addr[4:0]),
           .cpu_wdata                   (cpu_wdata[7:0]));
   
   BB BB_U(/*AUTOINST*/
           // Outputs
           .mbist_rst                   (mbist_rst),
           .mbist_test                  (mbist_test),
           // Inputs
           .clock                               (clock),
           .reset                               (reset),
           .test_enable                 (test_enable),
           .core_code_idle                      (core_code_idle),
           .core_code_error             (core_code_error),
           .core_data                   (core_data[7:0]),
           .mbist_done                  (mbist_done[8:0]),
           .mbist_fail                  (mbist_fail[8:0]));
   
   // Local Variables:
   // verilog-library-directories:(".")
   // End:
   
endmodule
