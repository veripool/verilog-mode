module sc_top (
  input var real  Tx_vcm,
  input var real  i_DAC_in,
  input           i_Tx_SC_en,
  output var real Tx_vsc
);

endmodule


module cm_top (
  input           i_Tx_CM_en,
  output var real Tx_vcm
);

endmodule

module top (
/*AUTOOUTPUT*/
/*AUTOINPUT*/
);

/*AUTOWIRE*/

cm_top cm_buf (/*AUTOINST*/);

sc_top sc_buf (/*AUTOINST*/);

endmodule
