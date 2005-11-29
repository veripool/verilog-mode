//From: "Chris Kappler" <ckappler@hhnetwk.com>

//Verilint 440 off // WARNING: Clock is used as a reset
//Verilint 394 off // WARNING: Multiple clocks in the always block
//Verilint  71 off // WARNING: Case statement without default clause

module x (/*AUTOARG*/
   // Outputs
   a, b, c,
   // Inputs
   clk, reset_l, in_a, in_b, in_c
   );

   input clk, reset_l, in_a,in_b,in_c;
   output a,b,c;
   reg 	  a,b,c;

   always @(posedge clk or negedge reset_l) begin
      if (!reset_l) begin
         c <= 1;
         /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 a <= #1 0;
	 b <= #1 0;
	 // End of automatics
      end
      else begin
         a <= in_a;
         b <= in_b;
         c <= in_c;
      end
   end

   always @(posedge clk or negedge reset_l) begin
      casex ({reset_l,in_a})
	2'b1_x: begin
           a <= in_a;
           b <= in_b;
           c <= in_c;
        end
	2'b0_x: begin
           c <= 1;
           /*AUTORESET*/
	   // Beginning of autoreset for uninitialized flops
	   a <= #1 0;
	   b <= #1 0;
	   // End of automatics
        end
      endcase
   end

   always @(/*AS*/in_a or in_b or reset_l) begin
      casex ({reset_l,in_a})
	2'b1_x: begin
           a = in_a;
           b = in_b;
        end
	2'b0_x: begin
           c = 1;
           /*AUTORESET*/
	   // Beginning of autoreset for uninitialized flops
	   a = 0;
	   b = 0;
	   // End of automatics
        end
      endcase
   end

endmodule

// Local Variables:
// verilog-auto-reset-widths: nil
// verilog-assignment-delay: "#1 "
// End:
