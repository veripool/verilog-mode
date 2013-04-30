module mod1(input logic [1:0] reg1[4],
            input logic                   reg2[5][6],
            input logic [1:0] [3:0] [2:0] reg4);
endmodule

module mod2(output logic [1:0] reg1[4],
            output logic [1:0] [3:0] [2:0] reg4);
endmodule

module dut (
            /*AUTOINPUT*/
            // Beginning of automatic inputs (from unused autoinst inputs)
            input logic reg2 [5][6]         // To foo_i of mod1.v
            // End of automatics
            /*AUTOOUTPUT*/
            );
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [1:0]            reg1 [4]; // From drv_i of mod2.v
   logic [1:0][3:0] [2:0] reg4;                 // From drv_i of mod2.v
   // End of automatics
   
   mod1 foo_i(/*AUTOINST*/
              // Inputs
              .reg1                     (reg1/*[1:0]*/),
              .reg2                     (reg2),
              .reg4                     (reg4/*[3:0][1:0][2:0]*/));
   
   /* drv_i AUTO_TEMPLATE (.reg1(reg1[]), );*/
   mod2 drv_i(/*AUTOINST*/
              // Outputs
              .reg1                     (reg1/*[1:0]*/),
              .reg4                     (reg4/*[3:0][1:0][2:0]*/));
endmodule
