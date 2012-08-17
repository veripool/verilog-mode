
module auto_module
  ( input my_clk,
    input  my_rst_n,
    
    
    /*AUTOINOUTMODPORT("automodport_if" "pure_mp")*/
    // Beginning of automatic in/out/inouts (from modport)
    output out_pure,
    input  in_pure,
    // End of automatics
    //ex: input in_pure;
    //ex: output        out_pure;
    
    /*AUTOINOUTMODPORT("automodport_if" "req_mon_mp")*/
    // Beginning of automatic in/out/inouts (from modport)
    input  req_credit,
    input  req_dat,
    input  req_val,
    input  rst_n,
    // End of automatics
    //ex: input                 req_credit,             // To auto_i of auto_intf.sv
    //ex: input [63:0]          req_data,               // To auto_i of auto_intf.sv
    //ex: input                 req_val,                // To auto_i of auto_intf.sv
    
    /*AUTOINOUTMODPORT("automodport_if" "rsp_drv_mp")*/
    // Beginning of automatic in/out/inouts (from modport)
    output rsp_data,
    output rsp_cmd,
    input  rsp_credit
    // End of automatics
    //ex: output [1:0]          rsp_cmd,                // From auto_i of auto_intf.sv
    //ex: input                 rsp_credit,             // To auto_i of auto_intf.sv
    //ex: output [63:0]         rsp_data                // From auto_i of auto_intf.sv
    );
   
   auto_intf auto_i
     (// Inputs
      .clk              (my_clk),
      .rst_n            (my_rst_n));
   
   /*AUTOASSIGNMODPORT("automodport_if" "req_mon_mp" "auto_i" )*/
   // Beginning of automatic assignments from modport
   assign auto_i.req_credit  = req_credit;
   assign auto_i.req_dat  = req_dat;
   assign auto_i.req_val  = req_val;
   // End of automatics
   //ex: assign auto_i.req_credit         = req_credit;
   //ex: assign auto_i.req_data           = req_data;
   //ex: assign auto_i.req_val            = req_val;
   
   /*AUTOASSIGNMODPORT("automodport_if" "rsp_drv_mp" "auto_i" )*/
   // Beginning of automatic assignments from modport
   assign rsp_cmd  = auto_i.rsp_cmd;
   assign rsp_data  = auto_i.rsp_data;
   assign auto_i.rsp_credit  = rsp_credit;
   // End of automatics
   //ex: assign rsp_cmd                   = auto_i.rsp_cmd;
   //ex: assign rsp_data                  = auto_i.rsp_data;
   //ex: assign auto_i.rsp_credit         = rsp_credit;
   
   initial begin
      `cn_set_intf(virtual auto_intf.req_mon_mp, "auto_pkg::auto_intf", "req_mon_vi", auto_i.req_mon_mp );
      `cn_set_intf(virtual auto_intf.rsp_drv_mp, "auto_pkg::auto_intf", "rsp_drv_vi", auto_i.rsp_drv_mp );
   end
   
endmodule
