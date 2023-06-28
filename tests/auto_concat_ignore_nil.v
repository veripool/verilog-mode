module xyz (/*AUTOARG*/
   // Outputs
   signal_f, signal_e, signal_d,
   // Inputs
   signal_c, signal_b, signal_a
   );

   // when verilog-auto-ignore-concat:nil, all signals are recongnized as IOs

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		signal_a;		// To u_abc of abc.v
   input		signal_b;		// To u_abc of abc.v
   input [1:0]		signal_c;		// To u_abc of abc.v
   // End of automatics

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		signal_d;		// From u_abc of abc.v
   output		signal_e;		// From u_abc of abc.v
   output		signal_f;		// From u_abc of abc.v
   // End of automatics

   /*AUTOWIRE*/

   /* abc AUTO_TEMPLATE
     (
      // Outputs
      .signal_d				({signal_d}),
      .signal_e				((signal_e)),
      // Inputs
      .signal_a				({signal_a}),
      .signal_b				((signal_b)),
    );*/

   abc u_abc
     (/*AUTOINST*/
      // Outputs
      .signal_d				({signal_d}),		 // Templated
      .signal_e				((signal_e)),		 // Templated
      .signal_f				(signal_f),
      // Inputs
      .signal_a				({signal_a}),		 // Templated
      .signal_b				((signal_b)),		 // Templated
      .signal_c				(signal_c[1:0]));

endmodule // xyz

module abc (/*AUTOARG*/
   // Outputs
   signal_d, signal_e, signal_f,
   // Inputs
   signal_a, signal_b, signal_c
   );

   input [1:0] signal_a;
   input [1:0] signal_b;
   input [1:0] signal_c;
   output signal_d;
   output signal_e;
   output signal_f;

endmodule // abc

// Local Variables:
// verilog-auto-ignore-concat: nil
// End:
