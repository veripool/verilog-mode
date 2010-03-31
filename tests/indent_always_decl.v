module foo ();
   // Before the always block,
   // indents to here: (which I like)
   //          V
   wire [10:0] mux_output0 =
               select0[0] ? mux_input0 :
               select0[1] ? mux_input1 :
               select0[2] ? mux_input2 :
               select0[3] ? mux_input3 :
               select0[4] ? mux_input4 :
               select0[5] ? mux_input5 :
               select0[6] ? mux_input6 :
               mux_input7;
   
   reg 	       foobar;
   always @(posedge clk)
     if (reset_n) begin
        foobar <= 1'b0;
     end
   
   // After the always block,
   // indents to here:
   //                       V
   wire [10:0] mux_output1 =
               select1[0] ? mux_input8 :
               select1[1] ? mux_input9 :
               select1[2] ? mux_input10 :
               select1[3] ? mux_input11 :
               select1[4] ? mux_input12 :
               select1[5] ? mux_input13 :
               select1[6] ? mux_input14 :
               mux_input15;
endmodule

