// See bug75

module autoinst_interface
  (/*AUTOINOUTMODULE("autoinst_interface_sub")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output logic [7:0] count,
   input logic        clk,
   input logic        reset,
   input logic        start,
   my_svi.master my_svi_port,
   my_svi my_svi_noport,
   my_svi my_svi_noport_upper_decl
   // End of automatics
   );
endmodule

module autoinst_interface
  (/*AUTOINOUTCOMP("autoinst_interface_sub")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output logic      clk,
   output logic      reset,
   output logic      start,
   input logic [7:0] count,
   my_svi.master my_svi_port,
   my_svi my_svi_noport,
   my_svi my_svi_noport_upper_decl
   // End of automatics
   );
endmodule

module top;
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [7:0] count;                   // From submod0 of autoinst_interface_sub.v
   // End of automatics
   
   my_svi               my_svi_noport_upper_decl ();
   
   autoinst_interface_sub submod0 (/*AUTOINST*/
                                   // Interfaces
                                   .my_svi_port         (my_svi_port.master),
                                   .my_svi_noport       (my_svi_noport),
                                   .my_svi_noport_upper_decl(my_svi_noport_upper_decl),
                                   // Outputs
                                   .count               (count[7:0]),
                                   // Inputs
                                   .clk                 (clk),
                                   .reset               (reset),
                                   .start               (start));
endmodule
