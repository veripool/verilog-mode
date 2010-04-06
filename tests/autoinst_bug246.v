module foo1 (/*AUTOARG*/
   // Outputs
   Z, Z0,
   // Inputs
   A, B
   );
input [31:0] A;
input [31:0] B;

output [15:0] Z;
output [7:0] Z0;

assign Z = A + B;
endmodule

module foo (/*AUTOARG*/
   // Outputs
   Z,
   // Inputs
   A, B
   );
input [31:0] A;
input [31:0] B;

output [15:0] Z;

assign Z = A + B;
endmodule

module foo_top (/*AUTOARG*/
   // Outputs
   Z,
   // Inputs
   A, B
   );
/*AUTOOUTPUT*/
// Beginning of automatic outputs (from unused autoinst outputs)
output [15:0]		Z;			// From foo of foo.v
// End of automatics
/*AUTOINPUT*/
// Beginning of automatic inputs (from unused autoinst inputs)
input [31:0]		A;			// To foo1 of foo1.v
input [31:0]		B;			// To foo1 of foo1.v, ...
// End of automatics
// End of automatics
/*AUTOWIRE*/
// Beginning of automatic wires (for undeclared instantiated-module outputs)
wire [7:0]		Z0_int;			// From foo1 of foo1.v
wire [15:0]		Z_int;			// From foo1 of foo1.v
// End of automatics

/*
foo1 AUTO_TEMPLATE
	(
	.Z(Z_int[]),
	.Z0(Z0_int[]),
	);
*/
foo1 foo1 (/*AUTOINST*/
	   // Outputs
	   .Z				(Z_int[15:0]),		 // Templated
	   .Z0				(Z0_int[7:0]),		 // Templated
	   // Inputs
	   .A				(A[31:0]),
	   .B				(B[31:0]));

/*
foo AUTO_TEMPLATE
	(
	.A({{4{1'b0}},Z_int[15:0],{4{1'b0}},Z0_int[7:0]}),
	);
*/
foo foo (/*AUTOINST*/
	 // Outputs
	 .Z				(Z[15:0]),
	 // Inputs
	 .A				({{4{1'b0}},Z_int[15:0],{4{1'b0}},Z0_int[7:0]}), // Templated
	 .B				(B[31:0]));

// Works with
// .A({4'h0,Z_int[15:0],4'h0,Z0_int[7:0]}),   

endmodule
