module soft_rst ( 
		  // System clock and reset
		  input  clk,
		  input  rst_n,
			 
			 // Interface to software land
		  input  req_soft_rst, // Soft reset request
		  output soft_rst_dne, // Soft reset done
			 
			 // Interface to other modules
		  output dma_halt, // Reset pending, halt activity
		  input  tx_quiet, // TX side is dormant
		  input  rx_quiet, // RX side is dormant
		  output soft_rst, // Soft (sync) reset to VC3 side
		  output hs_async_rst_n // Async reset to host side
		  );
   
   reg [1:0] 		 state;
   
   localparam [1:0] IDLE  = 2'h0,
     HALT 		  = 2'h1,
     RST 		  = 2'h2,
     DONE 		  = 2'h3;
   
endmodule // soft_rst
