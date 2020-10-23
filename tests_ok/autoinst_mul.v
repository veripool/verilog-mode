// issue 1698

module sub_mod
  (
   input [8+4-1:0][7:0] add_left,
   input [8-4-1:0][7:0] substract_left,
   input [8*4-1:0][7:0] multiply_left,
   input [8/4-1:0][7:0] divide_left
   
   input [7:0][8+4-1:0] add_right,
   input [7:0][8-4-1:0] substract_right,
   input [7:0][8*4-1:0] multiply_right,
   input [7:0][8/4-1:0] divide_right,
   );
endmodule : sub_mod

module top_mod
  (
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [8+4-1:0] [7:0] add_left, // To sub_mod_i of sub_mod.v
   input [7:0] [11:0]    add_right, // To sub_mod_i of sub_mod.v
   input [8/4-1:0] [7:0] divide_left, // To sub_mod_i of sub_mod.v
   input [7:0] [1:0]     divide_right, // To sub_mod_i of sub_mod.v
   input [8*4-1:0] [7:0] multiply_left, // To sub_mod_i of sub_mod.v
   input [7:0] [31:0]    multiply_right, // To sub_mod_i of sub_mod.v
   input [8-4-1:0] [7:0] substract_left, // To sub_mod_i of sub_mod.v
   input [7:0] [3:0]     substract_right        // To sub_mod_i of sub_mod.v
   // End of automatics
   );
   
   sub_mod sub_mod_i
     (/*AUTOINST*/
      // Inputs
      .add_left                 (add_left/*[8+4-1:0][7:0]*/),
      .substract_left                   (substract_left/*[8-4-1:0][7:0]*/),
      .multiply_left                    (multiply_left/*[8*4-1:0][7:0]*/),
      .divide_left                      (divide_left/*[8/4-1:0][7:0]*/),
      .add_right                        (add_right/*[7:0][8+4-1:0]*/),
      .substract_right                  (substract_right/*[7:0][8-4-1:0]*/),
      .multiply_right                   (multiply_right/*[7:0][8*4-1:0]*/),
      .divide_right                     (divide_right/*[7:0][8/4-1:0]*/));
endmodule
