module sub;
   parameter AA, AB, AC;
   output    ia, ib, ic;
endmodule

module autoinst_regexp_inst;
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire ia; // From sub0 of sub.v, ...
   wire ib; // From sub0 of sub.v, ...
   wire ic;                     // From sub0 of sub.v, ...
   // End of automatics
   
   // We don't yet support AUTO INST with a parameter
   
   sub
     #(/*AUTOINSTPARAM("AB")*/
       // Parameters
       .AB                              (AB))
   sub0
     (/*AUTOINST*/
      // Outputs
      .ia                               (ia),
      .ib                               (ib),
      .ic                               (ic));
   
   sub
     sub1
       (/*AUTOINST("ia")*/
        // Outputs
        .ia                             (ia));
   
   sub
     sub1
       (/*AUTOINST("?!ia")*/
        // Outputs
        .ib                             (ib),
        .ic                             (ic));
   
endmodule
