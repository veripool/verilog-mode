// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

// Reported by Julian Gorfajn <jig1@cornell.edu>

module autoinst_multitemplate ();

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		Boo2;			// To suba2 of SubB.v
   input		Boo3;			// To suba3 of SubB.v
   input		a;			// To suba2 of SubB.v
   input		b;			// To suba3 of SubB.v
   // End of automatics

   /*AUTOOUTPUT*/

   /*AUTOWIRE*/

   wire [3:0] 		f4_dotnamed;

   /*
     SubB AUTO_TEMPLATE (
     .b (Boo@),
    );*/

   SubB suba2 (/*AUTOINST*/
	       // Inputs
	       .a			(a),
	       .b			(Boo2));			 // Templated

   /*
     SubB AUTO_TEMPLATE (
     .a (Boo@),
    );*/

   SubB suba3 (/*AUTOINST*/
	       // Inputs
	       .a			(Boo3),			 // Templated
	       .b			(b));

// Test harness doesn't support expected errors
//   /*
//     SubUnused AUTO_TEMPLATE (
//     .subunused (Boo@),
//    );*/

endmodule

module SubB (input a,input b);
endmodule

// Local Variables:
// verilog-auto-template-warn-unused: t
// End:
