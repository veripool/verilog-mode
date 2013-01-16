typedef struct packed {
  logic			a,b,c;
} tTest;

module test
  (
   input clk,rst
   );

   wire [7:0] data_tm;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   tTest		q;			// From foo of foo.v
   // End of automatics

   /* foo AUTO_TEMPLATE (
    .tm			(data_tm),
    );
    */

   foo foo (/*AUTOINST*/
	    // Outputs
	    .q				(q),
	    // Inputs
	    .clk			(clk),
	    .rst			(rst),
	    .tm				(data_tm));		 // Templated
   /*AUTO_LISP(setq verilog-typedef-regexp "^t[A-Z]")*/
endmodule

module foo
  (
   input       clk,
   input       rst,
   input [7:0] tm,
   output      tTest q
   );
endmodule

// Local Variables:
// verilog-case-fold:nil
// verilog-library-directories:(".")
// verilog-typedef-regexp:"^t[A-Z]"
// End:
