module autoinst_wildcard;

   /* sub AUTO_TEMPLATE (
    .a\(.\)\(.\)  (@"(substring vl-cell-name 4 5)"_@"(substring vl-cell-name 6 7)"_a_\1_\2),
    ); */

   sub sub_0_0 (/*AUTOINST*/);
   sub sub_0_1 (/*AUTOINST*/);
   sub sub_1_0 (/*AUTOINST*/);
   sub sub_1_1 (/*AUTOINST*/);

   /* sub AUTO_TEMPLATE (
    .a\(.\)\(.\)  (b_\1_\2),
    ); */

   sub sub_0_0 (/*AUTOINST*/);
   sub sub_0_1 (/*AUTOINST*/);
   sub sub_1_0 (/*AUTOINST*/);
   sub sub_1_1 (/*AUTOINST*/);

endmodule

module sub;
   input a33, a34, a44, a43;
endmodule

// Local Variables:
// verilog-auto-inst-template-numbers: t
// End:
