module ex;
   
   // Note "inst" below should be vl-inst, but allowed for historical usage
   
   /* autoinst_paramover_sub AUTO_TEMPLATE (
    .a(@"vl-cell-name"_in[]),
    .b(@"(substring inst 2)"_out[]),
    );*/
   
   autoinst_paramover_sub u_a0(/*AUTOINST*/
                               // Inouts
                               .a               (u_a0_in[bitsa:0]), // Templated
                               .b               (a0_out[bitsb:0])); // Templated
   
   autoinst_paramover_sub u_a1(/*AUTOINST*/
                               // Inouts
                               .a               (u_a1_in[bitsa:0]), // Templated
                               .b               (a1_out[bitsb:0])); // Templated
   
endmodule
