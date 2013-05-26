module InstMod ( ins, outs );
    output [INWIDTH-1:0] ins;
endmodule

module test (/*AUTOARG*/) ;
  parameter foo=1;
  /*
  parameter foo=2;
  */                                                                                                                                           

   //bug647

   /* InstMod AUTO_TEMPLATE
    (.ins    (a@"vh-foo")); */

   InstMod instName (/*AUTOINST*/
		     // Outputs
		     .ins		(a1));			 // Templated

endmodule

// Local Variables:
// eval:(verilog-read-defines)
// End:
