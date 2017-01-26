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
   /* could have [extern] [virtual] [protected|local] task [static|automatic|] name (); */
   /* If extern -> then it is complete; other wise it is not complete */
   /* class could have:
    class c
    extern virtual static protected task t ();
    endclass
    task declaration could have
    task static t();
    endtask
    */
   class c;
   endclass // c
   function f();
      g;
   endfunction // f
   generate g;
      /* a lot of stuff */
   endgenerate
   task t();
      /**/
      /**/
   endtask // t
   protected virtual task pv_t();
      /**/
   endtask // pv_t
   
   protected task p_t();
      /* ACK*/
   endtask // p_t
   virtual task v_t();
      /**/
   endtask // v_t
   virtual protected task vp_t();
      /**/
   endtask // vp_t
   protected virtual task pv_t();
      /**/
   endtask // pv_t
   extern task e_t();
   extern virtual task ev_t();
   extern protected task ep_t();
   extern protected virtual task epv_t();
   extern protected virtual task main();
   generate g;
      /**/
   endgenerate
   
   extern virtual function void reconfigure(burst_drv_cfg cfg);
   extern virtual function void reset_xactor(reset_e rst_type = SOFT_RST);
   extern virtual function new (
                                string inst,
                                int    stream_id,
                                burst_drv_cfg cfg = null,
                                burst_xn_channel in_chan = null,
                                burst_xn_channel obs_chan = null,
                                burst_xn rx_factory = null);
   virtual task start();
      super.start();
      this.tx_dma.start();
      this.rx_dma.start();
   endtask // start
   task start();
      super.start();
      this.tx_dma.start();
      this.rx_dma.start();
   endtask // start
   task static start();
      super.start();
      this.tx_dma.start();
      this.rx_dma.start();
   endtask // static
endclass : burst_drv

