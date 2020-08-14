
module top
  #(
    parameter         NOF_TEST = 6,
    parameter integer TEST [NOF_TEST] = '{10,20,30,40,50,60}
    )
   
   (
    /*AUTOINPUT*/
    /*AUTOOUTPUT*/
    // Beginning of automatic outputs (from unused autoinst outputs)
    output [(TEST[1] )-1:0] x                   // From inst of submod.v
    // End of automatics
    );
   
   /*submod  AUTO_TEMPLATE (
    .NUM_MEM        (TEST[1]),
    );
    */
   
   submod #( /*AUTOINSTPARAM*/
             // Parameters
             .NUM_MEM                   (TEST[1]))               // Templated
   inst
     (
      /*AUTOINST*/
      // Outputs
      .x                                (x[(TEST[1])-1:0]));
   
endmodule

module submod
  #(parameter  NUM_MEM        = 6
    )
   (output [NUM_MEM-1:0] x);
endmodule

// Local Variables:
// verilog-auto-inst-param-value:t
// End:
