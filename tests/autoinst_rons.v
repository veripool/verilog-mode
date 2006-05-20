module autoinst_rons;
   dwrr dwrr_inst (/*AUTOINST*/);
endmodule

// module declaration
module dwrr (
             //Inputs
    input [47:0] data_avail,
    input [47:0] cell_eof,

             //Outputs
    output reg [6:0]  dwell_count_out,
    output reg [47:0] eligible_flag,
    output [5:0]      dwrr_state );

endmodule
