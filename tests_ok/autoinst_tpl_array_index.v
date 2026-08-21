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
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [6:0] abc [0:2];  // From u_test2 of autoinst_tpl_array_index_sub.v, ...
   wire       sbit [0:2]; // From u_test2 of autoinst_tpl_array_index_sub.v, ...
   // End of automatics
   /*
    autoinst_tpl_array_index_sub AUTO_TEMPLATE
    (
    .test2 (abc[].[@]),
    .bitout (sbit[].[@]),
    );
    */
   autoinst_tpl_array_index_sub u_test2
     (/*AUTOINST*/
      // Outputs
      .test2                            (abc[2]/*[6:0].[2]*/),   // Templated
      .bitout                           (sbit[2]/*.[2]*/));      // Templated
   autoinst_tpl_array_index_sub u_test0
     (/*AUTOINST*/
      // Outputs
      .test2                            (abc[0]/*[6:0].[0]*/),   // Templated
      .bitout                           (sbit[0]/*.[0]*/));      // Templated
endmodule

// Same element index twice merges silently into a single-element range

module autoinst_tpl_array_index_dup
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [6:0] dup [1:1];    // From u_a1 of autoinst_tpl_array_index_sub.v, ...
   wire       dupbit [1:2]; // From u_a1 of autoinst_tpl_array_index_sub.v, ...
   // End of automatics
   /*
    autoinst_tpl_array_index_sub AUTO_TEMPLATE
    (
    .test2 (dup[].[1]),
    .bitout (dupbit[].[@]),
    );
    */
   autoinst_tpl_array_index_sub u_a1
     (/*AUTOINST*/
      // Outputs
      .test2                            (dup[1]/*[6:0].[1]*/),   // Templated
      .bitout                           (dupbit[1]/*.[1]*/));    // Templated
   autoinst_tpl_array_index_sub u_a2
     (/*AUTOINST*/
      // Outputs
      .test2                            (dup[1]/*[6:0].[1]*/),   // Templated
      .bitout                           (dupbit[2]/*.[2]*/));    // Templated
endmodule

// Non-numeric index is not combined, first one wins

module autoinst_tpl_array_index_nonnum
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [6:0] nn [IDX];    // From u_n1 of autoinst_tpl_array_index_sub.v, ...
   wire       nnbit [1:2]; // From u_n1 of autoinst_tpl_array_index_sub.v, ...
   // End of automatics
   /*
    autoinst_tpl_array_index_sub AUTO_TEMPLATE
    (
    .test2 (nn[].[IDX]),
    .bitout (nnbit[].[@]),
    );
    */
   autoinst_tpl_array_index_sub u_n1
     (/*AUTOINST*/
      // Outputs
      .test2                            (nn[IDX]/*[6:0].[IDX]*/), // Templated
      .bitout                           (nnbit[1]/*.[1]*/));     // Templated
   autoinst_tpl_array_index_sub u_n2
     (/*AUTOINST*/
      // Outputs
      .test2                            (nn[IDX]/*[6:0].[IDX]*/), // Templated
      .bitout                           (nnbit[2]/*.[2]*/));     // Templated
endmodule
