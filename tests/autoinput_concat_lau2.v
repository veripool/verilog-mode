module xyz (/*AUTOARG*/);

   /*AUTOINPUT*/

   /*AUTOOUTPUT*/

   /*AUTOWIRE*/

   /* abc AUTO_TEMPLATE
     (
      // Outputs
      .signal_c				(signal_c),
      // Inputs
      .signal_a				({1'b0, signal_f}),
      .signal_b				(signal_b[2:0]));
    */
   
   abc u_abc
     (/*AUTOINST*/);

   /* def AUTO_TEMPLATE
     (// Outputs
      .signal_f				(signal_f),
      // Inputs
      .signal_d				({1'b1, signal_c}),
      .signal_e				({2'b11, signal_e}));
    */
    
   def u_def
     (/*AUTOINST*/);
   
endmodule // xyz

module abc (/*AUTOARG*/);

   input [1:0] signal_a;
   input [2:0] signal_b;
   output signal_c;

endmodule // abc

module def (/*AUTOARG*/);

   input [1:0] signal_d;
   input [2:0] signal_e;
   output signal_f;

endmodule // def
