module AA(
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

module TOP(
           /*AUTOINPUT*/
           // Beginning of automatic inputs (from unused autoinst inputs)
           input        afe_ctrl, // To AA_U of AA.v
           input        clock, // To AA_U of AA.v
           input [4:0]  cpu_addr, // To AA_U of AA.v
           input [7:0]  cpu_wdata, // To AA_U of AA.v
           input        cpu_wr, // To AA_U of AA.v
           input        reset, // To AA_U of AA.v
           // End of automatics
           /*AUTOOUTPUT*/
           // Beginning of automatic outputs (from unused autoinst outputs)
           output       core_code_error, // From AA_U of AA.v
           output       core_code_idle, // From AA_U of AA.v
           output [7:0] core_data, // From AA_U of AA.v
           output [7:0] cpu_rdata                  // From AA_U of AA.v
           // End of automatics
           );
   
   genvar x;
   
   AA AA_U(
           // Inputs
           .test_enable                 (x),
           /*AUTOINST*/
           // Outputs
           .core_data                   (core_data[7:0]),
           .core_code_error             (core_code_error),
           .core_code_idle                      (core_code_idle),
           .cpu_rdata                   (cpu_rdata[7:0]),
           // Inputs
           .clock                               (clock),
           .reset                               (reset),
           .afe_ctrl                    (afe_ctrl),
           .cpu_wr                              (cpu_wr),
           .cpu_addr                    (cpu_addr[4:0]),
           .cpu_wdata                   (cpu_wdata[7:0]));
   
endmodule
