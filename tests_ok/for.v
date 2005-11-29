module lbm
  (/*AUTOARG*/
   // Outputs
   outgo,
   // Inputs
   income
   );

   input	[1:0]	income;
   output [1:0] 	outgo;
   reg [1:0] 		outgo;

   integer 		i;
   always @ (/*AUTOSENSE*/income) begin
      for (i=0; i<32; i=i+1) begin
	 outgo[i] = income[i];
      end
   end

   always @ (/*AUTOSENSE*/income) begin
      if (|income) begin
	 $display("[0%10t] %I-for.v: found %s \"quote\" ",
		  $time, ((|income)?"in":"out"));

      end
   end

endmodule
