// Child module
//   ... with interface modport specified in module header

module autoinst_mplist_child
  (
   // --------------------------------------------------------------------------
   // Port Declarations
   // --------------------------------------------------------------------------
   
   input        clk,
   input        reset_n,
                
                // Yeah, let's have an interface
                autoinst_mplist_mbl_if.slave msg_req_if,
                autoinst_mplist_mbl_if.master msg_resp_if,
   
   // There are likely other signals present, too
   output logic msg_busy,
   output logic mem_rd_req,
   input        mem_rd_gnt
   );
   
   // Really snazzy RTL follows...
   
endmodule

/*
 Local Variables:
 verilog-typedef-regexp:"_t$"
 verilog-library-directories:(".")
 verilog-library-extensions:(".sv")
 End:
 */
