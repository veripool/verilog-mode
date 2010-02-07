`define auto_trq #1     // clock to q delay
`define auto_tcq #1     // reset to q delay

module autoinst_crawford_array_a(/*AUTOARG*/
                                 // Outputs
                                 a_valid, a_data,
                                 // Inputs
                                 a_ready, clk, rst_n
                                 );
   
   // a interface
   output       a_valid;
   output [7:0] a_data;
   input        a_ready;
   
   // clock interface
   input        clk;
   input        rst_n;
   
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [7:0]    a_data;
   reg          a_valid;
   // End of automatics
   
   always @(posedge clk or negedge rst_n) begin
      if(~rst_n) begin
         a_valid <= `auto_trq 0;
         a_data  <= `auto_trq 0;
      end
      else begin
         if(a_ready) begin
            a_valid <= `auto_tcq 1;
            a_data  <= `auto_tcq 8'hcc;
         end
      end
   end
   
endmodule
