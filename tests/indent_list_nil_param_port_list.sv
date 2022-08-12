module param_port_list # (parameter integer PARAMETER_0 = 0, // Some comment
parameter integer PARAMETER_1 = 0,
parameter integer PARAMETER_2 = 1,
parameter integer PARAMETER_3 = 2,
parameter integer PARAMETER_4 = 3,
parameter integer PARAMETER_5 = 4, // Some other comment
parameter integer PARAM_6 = 5,
parameter integer PARAMETER7 = 6,
parameter integer PARAM_LONGER = 7,
parameter integer PARAM_EVEN_LONGER = 8, // Maybe more comments
parameter integer PARAMETER_10 = 9,
parameter integer PARAMETER_11 = 10,
parameter integer PARAMETER_12 = 11,
parameter integer PARAMETER_13 = 12)
(
input logic clk,
input logic rst_n,
input logic signal_1, // Random comment
input logic [PARAMETER_0-1:0] signal2,
input logic [PARAMETER_1-1:0] signal_longer_name,
input logic signal3,
output logic [PARAMETER_2-1:0] signal_other_name,
input logic [PARAMETER_3-1:0] another_signal,
output logic [PARAMETER_4-1:0] even_more_signals,
output logic output_signal,
output logic more_output_signals [PARAMETER_13],
input logic packed_array [PARAMETER_5][PARAMETER_6], // Another random comment
input logic [4:0][3:0] unpacked_array, // More comments
input logic [4:0] unpacked_array_2 // Last comment
);

typedef struct packed{
logic name1;
logic [1:0] name2;
logic name_3;
logic name_4;
} some_type_t;


endmodule



module param_port_list # (
parameter PARAMETER_0 = 0,
parameter integer PARAMETER_11 = 1,
parameter logic [3:0] PARAMETER_222 = 4'h0
)(
input logic clk,
input logic rst_n,
input logic [3:0] inputs, // Random comment
output logic [15:0] outputs
);


assign outputs[3:0] = inputs;

endmodule



class parameterized_class #(
type T1=int,
type T22=int,
type T333=int
) extends base_class;

T1 val;
T22 val2;
T333 val3;

endclass


class parameterized_class2 #(type T1=int,
type T22=int,
type T333=int) extends base_class;

T1 val;
T22 val2;
T333 val3;

endclass



// Local Variables:
// verilog-indent-lists: nil
// End:
