typedef class burst_drv;
   
   
class burst_drv extends vmm_xactor;
   
   int EXECUTING;
   int OBSERVED;
   int SUB_OBSERVED;
   
   protected burst_drv_cfg cfg;
   local     burst_drv_cfg reset_cfg;
   protected burst_xn       rx_factory;
   local     burst_xn       reset_rx_factory;
   
   burst_xn_channel in_chan;
   burst_xn_channel obs_chan;
   
   burst_xn tr_main; // Current transaction in main()
   
   extern protected virtual task main();
   extern virtual function void reconfigure(burst_drv_cfg cfg);
   extern virtual function void reset_xactor(reset_e rst_type = SOFT_RST);
   extern virtual function new (
				string     inst,
				int        stream_id,
				burst_drv_cfg   cfg 	       = null,
				burst_xn_channel in_chan       = null,
				burst_xn_channel obs_chan      = null,
				burst_xn         rx_factory    = null);
endclass : burst_drv
