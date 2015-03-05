
// Parent module
//   Specifies modport for interfaces in header.
//   Has child modules which do the same.

module autoinst_mplist
  (
   // --------------------------------------------------------------------------
   // Port Declarations
   // --------------------------------------------------------------------------

   input                           clk,
   input                           reset_n,

   // Top-level interfaces
   mbl_if.master                   msg_resp_if

   );

   mbl_if                    msg_req_if;   // Some internal interface

  // --------------------------------------------------------------------------
  // Packages and Local Declarations
  // --------------------------------------------------------------------------

  /*AUTOLOGIC*/


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
    (/*AUTOINST*/);


endmodule

/*
 Local Variables:
 verilog-typedef-regexp:"_t$"
 verilog-library-directories:(".")
 verilog-library-extensions:(".sv")
 End:
 */
