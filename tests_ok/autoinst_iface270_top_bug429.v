// See http://www.veripool.org/issues/show/429

module top;
   /*AUTOWIRE*/
   
   autoinst_iface270_sub inst_if (/*AUTOINST*/);
   
   ifio sub (/*AUTOINST*/
             // Interfaces
             .inst_if                   (inst_if));
   
endmodule

module ifio
  (autoinst_iface270_sub inst_if);
endmodule

// Local Variables:
// verilog-auto-inst-interfaced-ports: nil
// End:
