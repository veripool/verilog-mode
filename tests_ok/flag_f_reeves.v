
module flag_f_reeves
  (/*AUTOARG*/
   // Outputs
   q,
   // Inputs
   a
   ) ;
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output q; // From ibuf of flag_f_reeves_IBUF.v
   // End of automatics
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input  a;                    // To ibuf of flag_f_reeves_IBUF.v
   // End of automatics
   
   flag_f_reeves_IBUF ibuf
     (/*AUTOINST*/
      // Outputs
      .q                                (q),
      // Inputs
      .a                                (a));
   
endmodule
// Local Variables:
// verilog-library-flags: ("-f flag_f_reeves.vc")
// End:
