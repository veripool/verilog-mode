// bug437:  Indentation of continued assignment incorrect if first line ends with ']'
module foo
(input [63:0]  data_in,
 input         ctl_in,

output [63:0] data_out,
output        ctl_out);

assign data_out  = data_in[1] ? data_in[63:0]
:            64'h0;

endmodule
