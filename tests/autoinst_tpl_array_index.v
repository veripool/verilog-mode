module autoinst_tpl_array_index_sub
  (
   output [6:0] test2,
   output       bitout
   );
endmodule

// Instance index "[].[@]" connects one element of an unpacked array;
// AUTOWIRE combines the connected indexes into one array declaration.

module autoinst_tpl_array_index
  ();
   /*AUTOWIRE*/
   /*
    autoinst_tpl_array_index_sub AUTO_TEMPLATE
    (
    .test2 (abc[].[@]),
    .bitout (sbit[].[@]),
    );
    */
   autoinst_tpl_array_index_sub u_test2
     (/*AUTOINST*/);
   autoinst_tpl_array_index_sub u_test0
     (/*AUTOINST*/);
endmodule

// Same element index twice merges silently into a single-element range

module autoinst_tpl_array_index_dup
  ();
   /*AUTOWIRE*/
   /*
    autoinst_tpl_array_index_sub AUTO_TEMPLATE
    (
    .test2 (dup[].[1]),
    .bitout (dupbit[].[@]),
    );
    */
   autoinst_tpl_array_index_sub u_a1
     (/*AUTOINST*/);
   autoinst_tpl_array_index_sub u_a2
     (/*AUTOINST*/);
endmodule

// Non-numeric index is not combined, first one wins

module autoinst_tpl_array_index_nonnum
  ();
   /*AUTOWIRE*/
   /*
    autoinst_tpl_array_index_sub AUTO_TEMPLATE
    (
    .test2 (nn[].[IDX]),
    .bitout (nnbit[].[@]),
    );
    */
   autoinst_tpl_array_index_sub u_n1
     (/*AUTOINST*/);
   autoinst_tpl_array_index_sub u_n2
     (/*AUTOINST*/);
endmodule
