
// Parent module
//   Specifies modport for interfaces in header.
//   Has child modules which do the same.

module autoinst_mplist
  (
   // --------------------------------------------------------------------------
   // Port Declarations
   // --------------------------------------------------------------------------
   
   input clk,
   input reset_n,
   
   // Top-level interfaces
   mbl_if.master msg_resp_if
   
   );
   
   mbl_if                    msg_req_if;   // Some internal interface
   
   // --------------------------------------------------------------------------
   // Packages and Local Declarations
   // --------------------------------------------------------------------------
   
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic mem_rd_req; // From child of autoinst_mplist_child.v
   logic msg_busy;              // From child of autoinst_mplist_child.v
   // End of automatics
   
   
   // --------------------------------------------------------------------------
   // Module Body
   // --------------------------------------------------------------------------
   
   // For the module instance below, interface ports should be
   // connected (per standard AUTOINST fashion) but *without*
   // explicitly specifying the modport.
   //
   // VCS (and likely other Synopsys tools) don't expect to see a
   // modport being "respecified" here.
   
   autoinst_mplist_child child
     (/*AUTOINST*/
      // Interfaces
      .msg_req_if                       (msg_req_if.slave),
      .msg_resp_if                      (msg_resp_if),
      // Outputs
      .msg_busy                         (msg_busy),
      .mem_rd_req                       (mem_rd_req),
      // Inputs
      .clk                              (clk),
      .reset_n                          (reset_n),
      .mem_rd_gnt                       (mem_rd_gnt));
   
   
endmodule

/*
 Local Variables:
 verilog-typedef-regexp:"_t$"
 verilog-library-directories:(".")
 verilog-library-extensions:(".sv")
 End:
 */
