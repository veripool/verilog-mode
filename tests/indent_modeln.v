//-*- mode: Verilog; verilog-indent-level:3; indent-tabs-mode: nil; tab-width: 1 -*-

typedef class b4_c;

class i_sb_c extends base_sb_c;
   `uvm_register_cb(i_sb_c, sb_i_cb_c)

   //------------
   int drain_time_ns = 5000;

   //------------

   typedef struct {
      pem_intf_defs::pem_ncb_err_rsp_t  err_rsp;
      int         rcv_time;
   } ncbi_err_rsp_t;

   //------------
   int 		  duax = 5;

   int 		  trwed = 0;

endclass
