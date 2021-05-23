module xyz (/*AUTOARG*/
   // Outputs
   signal_f, signal_c,
   // Inputs
   signal_e3, signal_b
   );

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [2:0]		signal_b;		// To u_abc of abc.v
   input		signal_e3;		// To u_def of def.v
   // End of automatics

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output		signal_c;		// From u_abc of abc.v
   output		signal_f;		// From u_def of def.v
   // End of automatics

   /*AUTOWIRE*/

   /* abc AUTO_TEMPLATE
     (
      // Outputs
      .signal_c				(signal_c),
      // Inputs
      .signal_a				(signal_f),   // AUTONOHOOKUP
      .signal_b				(signal_b[2:0]));
    */
   
   abc u_abc
     (/*AUTOINST*/
      // Outputs
      .signal_c				(signal_c),		 // Templated
      // Inputs
      .signal_a				(signal_f),		 // Templated AUTONOHOOKUP
      .signal_b				(signal_b[2:0]));	 // Templated

   /* def AUTO_TEMPLATE
     (// Outputs
      .signal_f				(signal_f),
      // Inputs
      .signal_d				(signal_c),   // AUTONOHOOKUP
      .signal_e				(signal_e),   // AUTONOHOOKUP
      .signal_e2			(signal_e2),   // AUTONOHOOKUP
      .signal_e3			((signal_e3)),
      );
    */
    
   def u_def
     (/*AUTOINST*/
      // Outputs
      .signal_f				(signal_f),		 // Templated
      // Inputs
      .signal_d				(signal_c),		 // Templated AUTONOHOOKUP
      .signal_e				(signal_e),		 // Templated AUTONOHOOKUP
      .signal_e2			(signal_e2),		 // Templated AUTONOHOOKUP
      .signal_e3			((signal_e3)));		 // Templated
   
endmodule // xyz

module abc (/*AUTOARG*/
   // Outputs
   signal_c,
   // Inputs
   signal_a, signal_b
   );

   input [1:0] signal_a;
   input [2:0] signal_b;
   output signal_c;

endmodule // abc

module def (/*AUTOARG*/
   // Outputs
   signal_f,
   // Inputs
   signal_d, signal_e, signal_e2, signal_e3
   );

   input [1:0] signal_d;
   input [2:0] signal_e;
   input [3:0] signal_e2;
   input [3:0] signal_e3;
   output signal_f;

endmodule // def
