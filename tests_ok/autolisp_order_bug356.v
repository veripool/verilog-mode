module autolisp_top (/*AUTOARG*/);
   
   /* autolisp_inst AUTO_TEMPLATE (
    .\(.*\)A    (\1_@"(eval tense)"_A),
    .\(.*\)B    (\1_@"(eval tense)"_B),
    );
    */
   /* AUTO_LISP(setq tense "is") */
   autolisp_inst AUTOLISP_INST_I0
     (/*AUTOINST*/
      // Outputs
      .result                           (result),
      // Inputs
      .portA                            (port_is_A),             // Templated
      .busA                             (bus_is_A),              // Templated
      .portB                            (port_is_B),             // Templated
      .busB                             (bus_is_B));             // Templated
   
   /* AUTO_LISP(setq tense "was") */
   autolisp_inst AUTOLISP_INST_I1
     (/*AUTOINST*/
      // Outputs
      .result                           (result),
      // Inputs
      .portA                            (port_was_A),            // Templated
      .busA                             (bus_was_A),             // Templated
      .portB                            (port_was_B),            // Templated
      .busB                             (bus_was_B));            // Templated
   
endmodule


module autolisp_inst (/*AUTOARG*/
                      // Outputs
                      result,
                      // Inputs
                      portA, busA, portB, busB
                      );
   
   input       portA;
   input [3:0] busA;
   input       portB;
   input [1:0] busB;
   
   output      result;
   
endmodule
