// See also autoinst_defs

`define foo 6
`define bar 0

module autoinst_dedefine;
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [3:1] fourwide; // From sub of bar.v
   output       onewide; // From sub of bar.v
   output [5:0] varwide;                // From sub of bar.v
   // End of automatics
   /*AUTOWIRE*/
   
   /* bar AUTO_TEMPLATE (
    .\(.*\)     (@"(concat vl-name (verilog-symbol-detick-text vl-bits))"),
    ); */
   
   bar sub
     (/*AUTOINST*/
      // Outputs
      .onewide                          (onewide),               // Templated
      .fourwide                         (fourwide[3:1]),         // Templated
      .varwide                          (varwide[6-1:0]));       // Templated
   
endmodule

module bar;
   output               onewide;
   output [3:1]         fourwide;
   output [`foo-1:`bar] varwide;
endmodule

// Local Variables:
// verilog-auto-read-includes:t
// End:

