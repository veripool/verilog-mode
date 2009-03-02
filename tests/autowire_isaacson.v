module t;
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire			w11;			// From bp3 of FswBypassArbiter.v
   wire			w12;			// From bp3 of FswBypassArbiter.v
   // End of automatics
   /*AUTOREG*/

   wand 		w0;
   wor 			w1;
   tri0 		w2;
   tri1 		w3;
   triand		w4;
   trior		w5;
   trireg		w6;
   tri			w7;
   wire			w8;
   supply0		w9;
   supply1		w10;

   FswBypassArbiter bp3 (/*AUTOINST*/
			 // Outputs
			 .w0			(w0),
			 .w1			(w1),
			 .w2			(w2),
			 .w3			(w3),
			 .w4			(w4),
			 .w5			(w5),
			 .w6			(w6),
			 .w7			(w7),
			 .w8			(w8),
			 .w9			(w9),
			 .w10			(w10),
			 .w11			(w11),
			 .w12			(w12));

endmodule

module FswBypassArbiter (/*AUTOARG*/
   // Outputs
   w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12
   ) ;
   output       w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12;
endmodule
