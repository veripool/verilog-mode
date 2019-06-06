// See also autoinst_defs

`define foo 6
`define bar 0

module autoinoutmodule_dedefine(
   /*AUTOINOUTMODULE("bar")*/
   );
endmodule

module bar;
   output onewide;
   output [3:1] fourwide;
   output [`foo-1:`bar] varwide;
endmodule

// Local Variables:
// verilog-auto-read-includes:t
// End:

