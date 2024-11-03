module autoinst_autolocal(
                          /*AUTOINPUT*/
                          // Beginning of automatic inputs (from unused autoinst inputs)
                          input i1 // To a2 of a2.v
                          // End of automatics
                          /*AUTOOUTPUT*/
                          );
   /* a2 AUTO_TEMPLATE (
    .i1(i1),
    .o1(o1), // AUTOLOCAL
    ) */
   a2 a2( /*AUTOINST*/
          // Outputs
          .o1                           (o1),                    // Templated AUTOLOCAL
          // Inputs
          .i1                           (i1));                   // Templated 
endmodule

module a2 (
           input  i1,
           output o1
           );
endmodule

