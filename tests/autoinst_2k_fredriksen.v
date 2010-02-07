module top ();


   sub sub(/*AUTOINST*/
	   // Outputs
	   .b				(b[PARAM2:0]),
	   // Inputs
	   .a				(a[PARAM1:0]));

endmodule // top

module sub
  #(parameter PARAM1=2,
    PARAM2=3,
    PARAM3=6)
     ( input wire [PARAM1:0] a,
       output reg [PARAM2:0]   b
      );


endmodule
