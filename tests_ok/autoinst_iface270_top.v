// See http://www.veripool.org/issues/show/270

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
