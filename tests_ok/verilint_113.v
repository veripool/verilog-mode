module cdl_io (/*AUTOARG*/
               // Outputs
               topsig,
               // Inputs
               clk
               );
   
   input  clk;
   output topsig;
   
   //Verilint 113 off // WARNING: in macro RSV_CDLBASE_RDWR, Multiple drivers to a flipflop
          
   reg    topsig;
`define TOPSIG  {topsig}
   
   always @ (posedge clk) begin
      `TOPSIG <= #0 1'b1;
   end
   
   task direct_write;
      input val;
      begin
         `TOPSIG = val;
      end
   endtask
endmodule
