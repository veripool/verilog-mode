module InstName (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );
   input [7:0] in;
   output [7:0] out;
   wire [7:0] 	out = ~in;
endmodule // bottm

module top (/*AUTOARG*/
   // Outputs
   outgo,
   // Inputs
   incom
   );
   input [31:0] incom;
   output [31:0] outgo;

   /* AUTO_LISP(defun getparam2 (strg)
    (string-match "[^0-9]*[0-9]+[^0-9]*\\([0-9]+\\)" strg)
    (match-string 1 strg))*/
   /* InstName AUTO_TEMPLATE (
    .out (@),
    .in (@"(getparam2 vl-cell-name)"),
    );
    */

   InstName BT0_2 (/*AUTOINST*/
		   // Outputs
		   .out			(0),			 // Templated
		   // Inputs
		   .in			(2));			 // Templated
   InstName BT1_3 (/*AUTOINST*/
		   // Outputs
		   .out			(1),			 // Templated
		   // Inputs
		   .in			(3));			 // Templated
   InstName BT2_5 (/*AUTOINST*/
		   // Outputs
		   .out			(2),			 // Templated
		   // Inputs
		   .in			(5));			 // Templated
   InstName BT3_9 (/*AUTOINST*/
		   // Outputs
		   .out			(3),			 // Templated
		   // Inputs
		   .in			(9));			 // Templated

endmodule



