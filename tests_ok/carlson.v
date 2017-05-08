module x ();
   always @ (/*AUTOSENSE*/bus or in1 or in2 or reset) begin
      out4 = | bus;
      
      out7 = 1'b0; // pre-initialize output of case so default not needed
      case (bus[1:0])
        2'b00: out7 = in1;
        2'b01: out7 = in2;
        2'b10: out7 = reset;
`ifdef BEH
        default: begin
           out7 = 1'bX; // force VCS simulation to propagate X's from the bus signal
           $display ("\n Error, in module temp, bus[1:0] illegal value of 11\n");
        end
`endif
        
      endcase // case(bus[1:0])
   end
endmodule
