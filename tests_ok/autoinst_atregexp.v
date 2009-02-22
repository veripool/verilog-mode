module ex;
   
   /* autoinst_paramover_sub AUTO_TEMPLATE "u_\(.*\)" (
    .a(inA_@[]),
    .b(outA_@[]),
    );*/
   
   autoinst_paramover_sub u_foo(/*AUTOINST*/
                                // Inouts
                                .a              (inA_foo[bitsa:0]), // Templated
                                .b              (outA_foo[bitsb:0])); // Templated
   autoinst_paramover_sub u_bar(/*AUTOINST*/
                                // Inouts
                                .a              (inA_bar[bitsa:0]), // Templated
                                .b              (outA_bar[bitsb:0])); // Templated
   autoinst_paramover_sub u_baz(/*AUTOINST*/
                                // Inouts
                                .a              (inA_baz[bitsa:0]), // Templated
                                .b              (outA_baz[bitsb:0])); // Templated
   
   /* autoinst_paramover_sub AUTO_TEMPLATE (
    .a(inN_@[]),
    .b(outN_@[]),
    );*/
   
   autoinst_paramover_sub u_0_2(/*AUTOINST*/
                                // Inouts
                                .a              (inN_0[bitsa:0]), // Templated
                                .b              (outN_0[bitsb:0])); // Templated
   autoinst_paramover_sub u_1_3(/*AUTOINST*/
                                // Inouts
                                .a              (inN_1[bitsa:0]), // Templated
                                .b              (outN_1[bitsb:0])); // Templated
   
endmodule
