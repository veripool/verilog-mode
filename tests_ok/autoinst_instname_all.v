module ex;
   
   /* autoinst_paramover_sub AUTO_TEMPLATE (
    .\(.*\)(@"vl-cell-name"_\1),
    );*/
   
   autoinst_paramover_sub u_a0(/*AUTOINST*/
                               // Inouts
                               .a               (u_a0_a),        // Templated
                               .b               (u_a0_b));       // Templated
   
   autoinst_paramover_sub u_a1(/*AUTOINST*/
                               // Inouts
                               .a               (u_a1_a),        // Templated
                               .b               (u_a1_b));       // Templated
   
endmodule
