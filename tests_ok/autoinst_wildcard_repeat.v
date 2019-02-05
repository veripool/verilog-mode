module autoinst_wildcard_repeat;
   
   /* sub AUTO_TEMPLATE (
    .w_\(.*\)_\1   (match_\1),
    .w_\(.*\)   (hit_\1),
    ); */
   
   sub sub
     (/*AUTOINST*/
      // Inputs
      .w_a_a                            (match_a),               // Templated
      .w_bb_bb                          (match_bb),              // Templated
      .w_x_y                            (hit_x_y));              // Templated
   
endmodule

module sub;
   input w_a_a;
   input w_bb_bb;
   input w_x_y;
endmodule
