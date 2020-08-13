///bug1337

`ifdef N
module my_module
  #( parameter p = 1,
     parameter r = 2 )
   (
    output logic a,
    output logic b
    );
endmodule : my_module
`endif

module my_module_stub
  #(
    /*AUTOINOUTPARAM("my_module")*/
    // Beginning of automatic parameters (from specific module)
    parameter p,
    parameter r
    // End of automatics
    )
   (
    /*AUTOINOUTMODULE("my_module")*/
    // Beginning of automatic in/out/inouts (from specific module)
    output logic a,
    output logic b
    // End of automatics
    );
   
   /*AUTOTIEOFF*/
   // Beginning of automatic tieoffs (for this module's unterminated outputs)
   assign a = 1'h0;
   assign b = 1'h0;
   // End of automatics
   
endmodule : my_module_stub

// Local Variables:
// verilog-auto-tieoff-declaration: "assign"
// End:
