// Example module that doesn't instantiate
module appendix1 (/*AUTOARG*/
                  // Outputs
                  z,
                  // Inputs
                  i
                  );
   input  i;
   output z;
   
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg    z;
   // End of automatics
   
   /*AUTOWIRE*/
   
   always @ (/*AUTOSENSE*/i) begin
      z = i;
   end
endmodule

// Example module that does instantiate
module appendix2 (/*AUTOARG*/
                  // Outputs
                  z,
                  // Inputs
                  i
                  );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input          i; // To apx10 of appendix1.v, ...
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [11:10] z;                    // From apx10 of appendix1.v, ...
   // End of automatics
   
   /*AUTOREG*/
   
   /*AUTOWIRE*/
   
   /*
    appendix1 AUTO_TEMPLATE (
    .z  (z[@]),
    );
    */
   
   appendix1 apx10 (/*AUTOINST*/
                    // Outputs
                    .z                  (z[10]),                 // Templated
                    // Inputs
                    .i                  (i));
   
   appendix1 apx11 (/*AUTOINST*/
                    // Outputs
                    .z                  (z[11]),                 // Templated
                    // Inputs
                    .i                  (i));
   
endmodule
