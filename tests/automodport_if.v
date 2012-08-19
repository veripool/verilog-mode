interface automodport_if
( input logic clk,
  input logic rst_n
);

   //----------------------------------------------------------------------------------------
   // Group: Signals
   logic 		req_val;
   logic [63:0] 	req_dat;
   logic 		req_credit;

   logic [1:0] 		rsp_cmd;
   logic [63:0] 	rsp_data;
   logic 		rsp_credit;
   
   logic 		in_pure;
   logic 		out_pure;
   logic		manually_listed;

  //----------------------------------------------------------------------------------------
   // Group: Clocking blocks
   clocking req_mon_cb @(posedge clk);
      input 		rst_n;
      input 		req_val;
      input 		req_dat;
      input 		req_credit;
      input		manually_listed;
  endclocking : req_mon_cb

   clocking rsp_drv_cb @(posedge clk);
      input 		rst_n;
      output 		rsp_cmd;
      output 		rsp_data;
      input 		rsp_credit;
   endclocking : rsp_drv_cb

   //----------------------------------------------------------------------------------------
   // Group: Modports
   modport req_mon_mp(clocking req_mon_cb);
   modport rsp_drv_mp(clocking rsp_drv_cb, import rsp_reset);
   modport pure_mp(input in_pure, output out_pure);

   //----------------------------------------------------------------------------------------
   // Group: Methods
   function void rsp_reset();
      rsp_cmd = 2'b0;
      rsp_data = 64'b0;
   endfunction : rsp_reset

   //----------------------------------------------------------------------------------------
   // Group: Assertions
   logic [1:0] 		cmd_m1;

   always @(posedge clk) begin
      cmd_m1 <= rsp_cmd;
      if(rst_n) begin
         if($isunknown(req_val))                  `cn_err_intf(("Signal req_data_cycle is an X."));
         if(req_val==1'b1 & $isunknown(req_data)) `cn_err_intf(("Signal req_data is an X."));
         if($isunknown(req_credit))               `cn_err_intf(("Signal req_credit is an X."));

         if($isunknown(rsp_cmd))                  `cn_err_intf(("Signal rsp_cmd is an X."));
         if(cmd_m1!=2'b0 & $isunknown(rsp_data))  `cn_err_intf(("Signal rsp_data is an X."));
         if($isunknown(rsp_credit))               `cn_err_intf(("Signal rsp_credit is an X."));
      end
   end
   
endinterface
