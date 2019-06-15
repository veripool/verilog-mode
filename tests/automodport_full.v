
module auto_module
( input my_clk,
  input 	my_rst_n,


  output 	manually_listed,

  /*AUTOINOUTMODPORT("automodport_if" "pure_mp")*/
  //ex: input	in_pure;
  //ex: output	out_pure;

  /*AUTOINOUTMODPORT("automodport_if" "req_mon_mp")*/
  //ex: input			req_credit,		// To auto_i of auto_intf.sv
  //ex: input [63:0]		req_data,		// To auto_i of auto_intf.sv
  //ex: input			req_val,		// To auto_i of auto_intf.sv

  /*AUTOINOUTMODPORT("automodport_if" "rsp_drv_mp")*/
  //ex: output [1:0]		rsp_cmd,		// From auto_i of auto_intf.sv
  //ex: input			rsp_credit,		// To auto_i of auto_intf.sv
  //ex: output [63:0]		rsp_data		// From auto_i of auto_intf.sv
);

   auto_intf auto_i
     (// Inputs
      .clk		(my_clk),
      .rst_n		(my_rst_n));

   /*AUTOASSIGNMODPORT("automodport_if", "req_mon_mp", "auto_i" )*/
   //ex: assign auto_i.req_credit         = req_credit;
   //ex: assign auto_i.req_data           = req_data;
   //ex: assign auto_i.req_val            = req_val;

   /*AUTOASSIGNMODPORT("automodport_if", "rsp_drv_mp", "auto_i" )*/
   //ex: assign rsp_cmd                   = auto_i.rsp_cmd;
   //ex: assign rsp_data                  = auto_i.rsp_data;
   //ex: assign auto_i.rsp_credit         = rsp_credit;

   /*AUTOASSIGNMODPORT("automodport_if", "r.*", "auto_i" )*/


   initial begin
      `cn_set_intf(virtual auto_intf.req_mon_mp, "auto_pkg::auto_intf", "req_mon_vi", auto_i.req_mon_mp );
      `cn_set_intf(virtual auto_intf.rsp_drv_mp, "auto_pkg::auto_intf", "rsp_drv_vi", auto_i.rsp_drv_mp );
   end

endmodule
