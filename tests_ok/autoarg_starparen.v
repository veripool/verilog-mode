// bug #1829
module dut (/*autoarg*/
            // Outputs
            d,
            // Inputs
            clk, rst_n
            );
   input        clk;
   input        rst_n;
   output logic d;
   
   always @(* )
     begin
        d = 1'b0;
     end
   
endmodule
