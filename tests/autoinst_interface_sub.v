interface my_svi;
   logic enable;
   logic error;
   logic [7:0] count2;
   modport master (
                   input enable,
                   output error,
                   output count2);
endinterface

module autoinst_interface_sub
  (input wire clk,
   input wire reset,
   input wire start,
   output reg [7:0] count,
   my_svi.master my_svi_port,
   my_svi my_svi_noport,
   my_svi my_svi_noport_upper_decl
   );
endmodule
