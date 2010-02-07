module autoinst_rons;
   dwrr dwrr_inst (/*AUTOINST*/
                   // Outputs
                   .dwell_count_out     (dwell_count_out[6:0]),
                   .eligible_flag       (eligible_flag[47:0]),
                   .dwrr_state          (dwrr_state[5:0]),
                   // Inputs
                   .data_avail          (data_avail[47:0]),
                   .cell_eof            (cell_eof[47:0]));
endmodule

// module declaration
module dwrr (
             //Inputs
             input [47:0]      data_avail,
             input [47:0]      cell_eof,
             
             //Outputs
             output reg [6:0]  dwell_count_out,
             output reg [47:0] eligible_flag,
             output [5:0]      dwrr_state );
   
endmodule
