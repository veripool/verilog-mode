module autoinst_name_bug245 (
   );

   /*AUTOINPUT*/

   /*AUTOOUTPUT*/

   /*AUTOWIRE*/

   wire [3:0] 		f4_dotnamed;

   /*Sub AUTO_TEMPLATE (
    .dtmp_NO (d_NO),
    .etmp_dotnamed (etmp_dotnamed),
    );*/

   Sub sub (
	    .bign1_dotnamed,
	    // Outputs
	    .bign2_dotnamed,
	    /*AUTOINST*/);

endmodule

module Sub
  (
   input  logic clk,
   output [2:0] a_NO,
   output [3:0] f4_dotnamed,
   output bign1_dotnamed,
   output [1:0] bign2_dotnamed,
   output c_dotnamed,
   output dtmp_NO,
   output etmp_dotnamed,
   input \escaped*dot*named 
   );
endmodule

// Local Variables:
// verilog-auto-inst-dot-name: t
// verilog-auto-inst-vector: nil
// End:
module autoinst_name_bug245 (
   );

   /*AUTOINPUT*/

   /*AUTOOUTPUT*/

   /*AUTOWIRE*/

   wire [3:0] 		f4_dotnamed;

   /*Sub AUTO_TEMPLATE (
    .dtmp_NO (d_NO),
    .etmp_dotnamed (etmp_dotnamed),
    );*/

   Sub sub (
	    .bign1_dotnamed,
	    // Outputs
	    .bign2_dotnamed,
	    /*AUTOINST*/);

endmodule

module Sub
  (
   input  logic clk,
   output [2:0] a_NO,
   output [3:0] f4_dotnamed,
   output bign1_dotnamed,
   output [1:0] bign2_dotnamed,
   output c_dotnamed,
   output dtmp_NO,
   output etmp_dotnamed,
   input \escaped*dot*named 
   );
endmodule

// Local Variables:
// verilog-auto-inst-dot-name: t
// verilog-auto-inst-vector: nil
// End:
module autoinst_name_bug245 (
   );

   /*AUTOINPUT*/

   /*AUTOOUTPUT*/

   /*AUTOWIRE*/

   wire [3:0] 		f4_dotnamed;

   /*Sub AUTO_TEMPLATE (
    .dtmp_NO (d_NO),
    .etmp_dotnamed (etmp_dotnamed),
    );*/

   Sub sub (
	    .bign1_dotnamed,
	    // Outputs
	    .bign2_dotnamed,
	    /*AUTOINST*/);

endmodule

module Sub
  (
   input  logic clk,
   output [2:0] a_NO,
   output [3:0] f4_dotnamed,
   output bign1_dotnamed,
   output [1:0] bign2_dotnamed,
   output c_dotnamed,
   output dtmp_NO,
   output etmp_dotnamed,
   input \escaped*dot*named 
   );
endmodule

// Local Variables:
// verilog-auto-inst-dot-name: t
// verilog-auto-inst-vector: nil
// End:
