//-*- mode: Verilog; verilog-indent-level: 3; indent-tabs-mode: nil; tab-width: 1 -*-

module apl2c_connect(autoinoutmodport_type_intf ctl_i,
                     /*AUTOINOUTMODPORT("autoinoutmodport_type_intf",  "ctl_cb")*/
                     // Beginning of automatic in/out/inouts (from modport)
                     input [4:0] inst,
                     input       isel_t isel,
                     input       replay
                     // End of automatics
                     );
   
   /*AUTOASSIGNMODPORT("autoinoutmodport_type_intf", "ctl_cb", "ctl_i")*/
   // Beginning of automatic assignments from modport
   assign ctl_i.inst = inst;
   assign ctl_i.isel = isel;
   assign ctl_i.replay = replay;
   // End of automatics
   
endmodule

interface autoinoutmodport_type_intf(input logic clk, input logic rst_n);
   import uvm_pkg::*;
   import ap_defines::*;
   
   logic [4:0] inst;
   isel_t       isel;
   logic replay;
   
   clocking ctl_cb @(posedge clk);
      input inst;
      input isel;
      input replay;
   endclocking: ctl_cb
   
   modport ctl_mp(clocking ctl_cb);
   
endinterface

// Local Variables:
// verilog-typedef-regexp:"_t"
// End:
