// See bug75

module autoinst_interface
  (/*AUTOINOUTMODULE("autoinst_interface_sub")*/
   );
endmodule

module autoinst_interface
  (/*AUTOINOUTCOMP("autoinst_interface_sub")*/
   );
endmodule

module top;
   /*AUTOWIRE*/
   autoinst_interface_sub submod0 (/*AUTOINST*/);
endmodule
