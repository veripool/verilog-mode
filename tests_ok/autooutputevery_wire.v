module test (/*AUTOARG*/
             // Outputs
             stage2_bus, stage3_bus,
             // Inputs
             stage1_bus
             );
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output logic [7:0] stage3_bus; // From i_second of sub_module.v
   // End of automatics
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input logic [7:0]  stage1_bus; // To i_first of sub_module.v
   // End of automatics
   /*AUTOOUTPUTEVERY("^stage")*/
   // Beginning of automatic outputs (every signal)
   output logic [7:0] stage2_bus; // From i_first of sub_module.v
   // End of automatics
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [7:0]        stage2_bus;               // From i_first of sub_module.v
   // End of automatics
   /*AUTOREG*/
   
   /* sub_module AUTO_TEMPLATE
    (
    .i_\(.*\)      (stage1_\1[]),
    .o_\(.*\)      (stage2_\1[]),
    );  */
   
   sub_module i_first (/*AUTOINST*/
                       // Outputs
                       .o_bus           (stage2_bus[7:0]),       // Templated
                       // Inputs
                       .i_bus           (stage1_bus[7:0]));      // Templated
   
   /* sub_module AUTO_TEMPLATE
    (
    .i_\(.*\)      (stage2_\1[]),
    .o_\(.*\)      (stage3_\1[]),
    ); */
   
   sub_module i_second (/*AUTOINST*/
                        // Outputs
                        .o_bus          (stage3_bus[7:0]),       // Templated
                        // Inputs
                        .i_bus          (stage2_bus[7:0]));      // Templated
   
endmodule // test

module sub_module (/*AUTOARG*/
                   // Outputs
                   o_bus,
                   // Inputs
                   i_bus
                   );
   
   input logic [7:0]  i_bus ;
   output logic [7:0] o_bus ;
   
   assign o_bus = i_bus;
   
endmodule // sub_module
