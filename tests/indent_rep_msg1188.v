module test;
   input  i_blc, I_cdef;
   reg [par_a -1:0] b,c;

   always @ ( posedge CLK or negedge RSTN ) begin
      if(!RSTN) begin
	 b = {par_a{1'b0}};
      c = {par_a{1'b0}};
   end
      else begin
         b=i_blc+I_cdef;
         c=b;
      end
   end
endmodule // test
