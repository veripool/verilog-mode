// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

// Reported by Julian Gorfajn <jig1@cornell.edu>

module autoinst_multitemplate ();

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		Boo1;			// To suba1 of SubA.v
   input		Boo2;			// To suba2 of SubB.v
   input		Boo3;			// To suba3 of SubC.v
   input		b;			// To suba2 of SubB.v
   input		c;			// To suba3 of SubC.v
   // End of automatics

   /*AUTOOUTPUT*/

   /*AUTOWIRE*/

   wire [3:0] 		f4_dotnamed;

   /*
     SubA AUTO_TEMPLATE
     SubB AUTO_TEMPLATE
     SubC AUTO_TEMPLATE (
     .a (Boo@),
    );*/

   SubA suba1 (/*AUTOINST*/
	       // Inputs
	       .a			(Boo1));			 // Templated
   SubB suba2 (/*AUTOINST*/
	       // Inputs
	       .a			(Boo2),			 // Templated
	       .b			(b));
   SubC suba3 (/*AUTOINST*/
	       // Inputs
	       .a			(Boo3),			 // Templated
	       .c			(c));

endmodule

module SubA (input a);
endmodule

module SubB (input a,input b);
endmodule

module SubC (input a,input c );
endmodule
