module autoinst_unsigned_bug302;
   
   Sub #(/*AUTOINSTPARAM*/
         // Parameters
         .No1                           (No1),
         .No2                           (No2),
         .No3                           (No3)) u_Abc
     (/*AUTOINST*/
      // Inputs
      .ck                               (ck),
      .abc                              (abc/*[No1-1:0][31:0]*/));
   
endmodule

module Sub
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
