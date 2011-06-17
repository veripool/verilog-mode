module autoinst_wildcard;
   
   /* sub AUTO_TEMPLATE (
    .a\(.\)\(.\)  (@"(substring vl-cell-name 4 5)"_@"(substring vl-cell-name 6 7)"_a_\1_\2),
    ); */
   
   sub sub_0_0 (/*AUTOINST*/
                // Inputs
                .a33                    (0_0_a_3_3),             // Templated 4
                .a34                    (0_0_a_3_4),             // Templated 4
                .a44                    (0_0_a_4_4),             // Templated 4
                .a43                    (0_0_a_4_3));            // Templated 4
   sub sub_0_1 (/*AUTOINST*/
                // Inputs
                .a33                    (0_1_a_3_3),             // Templated 4
                .a34                    (0_1_a_3_4),             // Templated 4
                .a44                    (0_1_a_4_4),             // Templated 4
                .a43                    (0_1_a_4_3));            // Templated 4
   sub sub_1_0 (/*AUTOINST*/
                // Inputs
                .a33                    (1_0_a_3_3),             // Templated 4
                .a34                    (1_0_a_3_4),             // Templated 4
                .a44                    (1_0_a_4_4),             // Templated 4
                .a43                    (1_0_a_4_3));            // Templated 4
   sub sub_1_1 (/*AUTOINST*/
                // Inputs
                .a33                    (1_1_a_3_3),             // Templated 4
                .a34                    (1_1_a_3_4),             // Templated 4
                .a44                    (1_1_a_4_4),             // Templated 4
                .a43                    (1_1_a_4_3));            // Templated 4
   
   /* sub AUTO_TEMPLATE (
    .a\(.\)\(.\)  (b_\1_\2),
    ); */
   
   sub sub_0_0 (/*AUTOINST*/
                // Inputs
                .a33                    (b_3_3),                 // Templated 33
                .a34                    (b_3_4),                 // Templated 33
                .a44                    (b_4_4),                 // Templated 33
                .a43                    (b_4_3));                // Templated 33
   sub sub_0_1 (/*AUTOINST*/
                // Inputs
                .a33                    (b_3_3),                 // Templated 33
                .a34                    (b_3_4),                 // Templated 33
                .a44                    (b_4_4),                 // Templated 33
                .a43                    (b_4_3));                // Templated 33
   sub sub_1_0 (/*AUTOINST*/
                // Inputs
                .a33                    (b_3_3),                 // Templated 33
                .a34                    (b_3_4),                 // Templated 33
                .a44                    (b_4_4),                 // Templated 33
                .a43                    (b_4_3));                // Templated 33
   sub sub_1_1 (/*AUTOINST*/
                // Inputs
                .a33                    (b_3_3),                 // Templated 33
                .a34                    (b_3_4),                 // Templated 33
                .a44                    (b_4_4),                 // Templated 33
                .a43                    (b_4_3));                // Templated 33
   
endmodule

module sub;
   input a33, a34, a44, a43;
endmodule

// Local Variables:
// verilog-auto-inst-template-numbers: t
// End:
