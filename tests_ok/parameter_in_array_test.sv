module parameter_in_array_test
  #(
    parameter TEST = 6
    )
   (
    
    output                         port_out_array1 [TEST], // FIX  bug in 1-D unpacked array
    output [TEST+2-1:0]            port_out_array2 [TEST+2],
    output [TEST+3-1:0] [TEST+3:0] port_out_array3 ,
    
    input                          port_in_array1 [TEST+1],
    input [TEST+2-1:0]             port_in_array2 [TEST+2] ,
    input [TEST+3-1:0] [TEST+3:0]  port_in_array3 ,
    
    );
   
endmodule

module test();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire               port_out_array1 [8];  // From u_parameter_in_array_test of parameter_in_array_test.v
   wire [9:0]         port_out_array2 [10]; // From u_parameter_in_array_test of parameter_in_array_test.v
   wire [10:0] [11:0] port_out_array3;      // From u_parameter_in_array_test of parameter_in_array_test.v
   // End of automatics
   /*AUTOREG*/
   
   parameter_in_array_test
     #(
       .TEST(8)
       )
   u_parameter_in_array_test
     (
      /*AUTOINST*/
      // Outputs
      .port_out_array1                  (port_out_array1/*.[8]*/),
      .port_out_array2                  (port_out_array2/*[9:0].[10]*/),
      .port_out_array3                  (port_out_array3/*[10:0][11:0]*/),
      // Inputs
      .port_in_array1                   (port_in_array1/*.[9]*/),
      .port_in_array2                   (port_in_array2/*[9:0].[10]*/),
      .port_in_array3                   (port_in_array3/*[10:0][11:0]*/));
endmodule

// Local Variables:
// verilog-auto-inst-param-value:t
// fill-column: 1
// End:
