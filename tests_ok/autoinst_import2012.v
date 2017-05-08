//bug1159

interface bus (input clk, rst_n);
   
   logic we;
   logic re;
   logic sel;
   
   //ports for master module
   modport master (input clk, rst_n, sel, output re, we);
   
   //ports for slave modules
   modport slave (input clk, rst_n, re, we, output sel);
   
endinterface

package common_pkg;
   parameter NUM_SLAVES = 2;
   // typedefs ...
endpackage
   
module bus_mux
  import common_pkg::*;
   (// Interfaces
    bus.slave         bus_master,             // bus from master
    bus.master        bus_slave[NUM_SLAVES],  // bus to slave
    // Outputs
    output logic addr_fault_strb
    );
   
endmodule

module top;
   import common_pkg::*;
   
   bus   bus_master (.clk(clk), .rst_n(rst_n));
   bus   bus_slave [NUM_SLAVES](.clk(clk), .rst_n(rst_n));
   
   bus_mux ibus_mux (/*AUTOINST*/
                     // Interfaces
                     .bus_master                (bus_master.slave),
                     .bus_slave         (bus_slave.master/*.[NUM_SLAVES]*/),
                     // Outputs
                     .addr_fault_strb   (addr_fault_strb));
   
endmodule
