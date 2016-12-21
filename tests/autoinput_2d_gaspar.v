module try_top(/*autoarg*/
   // Outputs
   out_momo,
   // Inputs
   in_momo
   );

   //bug1105 - should be [1:0]

   /*autoinput*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [0] [127:0]	in_momo;		// To try0 of try1.v, ...
   // End of automatics
   /*autooutput*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [0] [127:0]	out_momo;		// From try0 of try1.v, ...
   // End of automatics


   /*  try1 auto_template "try\(.*\)" 
    (
    .out_momo                      (out_momo[@][]),
    .in_momo                       (in_momo[@][]),
    );*/

   
   try1 try0 (/*autoinst*/
	      // Outputs
	      .out_momo			(out_momo[0][127:0]),	 // Templated
	      // Inputs
	      .in_momo			(in_momo[0][127:0]));	 // Templated
   try1 try1 (/*autoinst*/
	      // Outputs
	      .out_momo			(out_momo[1][127:0]),	 // Templated
	      // Inputs
	      .in_momo			(in_momo[1][127:0]));	 // Templated


endmodule // try_top

module try1(/*autoarg*/
   // Outputs
   out_momo,
   // Inputs
   in_momo
   );

   input [127:0] in_momo;
   output [127:0] out_momo;
endmodule // try1
