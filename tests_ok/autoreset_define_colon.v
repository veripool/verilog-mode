// bug594
`define TABADR_EGR_MOD_MAP 7:0

module test (
             /*AUTOARG*/
             // Inputs
             clk, rst, addr
             );
   /*AUTOINPUT*/
   /*AUTOOUTPUT*/
   
   input                       clk;
   input                       rst;
   input [`TABADR_EGR_MOD_MAP] addr;
   
   
   reg [`TABADR_EGR_MOD_MAP]   addrD1;
   reg [`TABADR_EGR_MOD_MAP]   addrD2;
   
   always @(posedge clk or posedge rst) begin
      if (rst_l) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         addrD1 <= '0/*NOWIDTH*/;
         addrD2 <= '0/*NOWIDTH*/;
         // End of automatics
      end
      else begin
         addrD1 <= addr ;
         addrD2 <= addrD1;
      end
   end
endmodule
