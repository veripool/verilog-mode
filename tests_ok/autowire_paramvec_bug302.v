module Abc_TEST ();
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [5:0] [31:0] abc;                      // From u_Def of Def.v
   // End of automatics
   
   Abc #(
         .No1                            (6),
         /*AUTOINSTPARAM*/
         // Parameters
         .No2                           (No2),
         .No3                           (No3)) u_Abc
     (
      /*AUTOINST*/
      // Inputs
      .ck                                       (ck),
      .abc                                      (abc/*[5:0][31:0]*/));
   
   Def #(
         .No1                            (6)) u_Def
     (
      // Outputs
      .ck                                  (ck),
      /*AUTOINST*/
      // Outputs
      .abc                                      (abc/*[5:0][31:0]*/));
   
endmodule


module Abc
  #(
    parameter No1 = 6,
    parameter int unsigned No2 // Parameter no. 2
                           = pa_Abc::No2,
    parameter bit          No3 [No1:0][No2-1:0] // Parameter no. 3
    = pa_Abc::No3
    )
   (
    input logic                 ck,
    input logic [No1-1:0][31:0] abc
    input logic [No1-1:0][31:0] abc
    );
endmodule

module Def
  #(
    parameter No1 = 6
    )
   (
    input logic                  ck,
    output logic [No1-1:0][31:0] abc
    );
endmodule

// Local Variables:
// verilog-library-extensions:(".v" ".sv")
// verilog-auto-inst-param-value:t
// End:
