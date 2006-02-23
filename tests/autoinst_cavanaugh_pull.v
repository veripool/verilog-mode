
module fifo(/*AUTOARG*/);

input     clk;                          
input     rst_n;                        
output    fifo_full_w;                  

input     enqueue_w;                    
input [(DATA_WIDTH-1):0] data_in_w;     

output                   data_valid_r;  
input                    dequeue_w;     
input [1:0]              full_threshold; 

output [(DATA_WIDTH-1):0] rdata_r;      


endmodule

module req (p_clk, carb_rst_rnp, req_rp, len_rxp, deq_req, deq_len, deq_val);

   input p_clk; 
   input carb_rst_rnp; 
   input [4:0] len_rxp; 
   input       req_rp; 
   input       deq_req; 
   output [4:0] deq_len; 
   output 	deq_val; 
   reg [5:0] 	fifo_entry1_rp;
   reg [5:0] 	fifo_entry2_rp;
   reg [4:0] 	deq_len; 
   reg 		deq_val;

endmodule

module pull( /*AUTOARG*/);

   input clk; 
   input rst_rnpha; 
   input [4:0] lenar_rxp; 
   input       rem_rpd; 
   input       d_rews; 
   output [4:0] d_len; 
   output 	d_val; 


/*   req AUTO_TEMPLATE "\(g[a-z0-9]+\|g.*[0-9]\)" (
                             .p_clk (my_clk_@),
                             .len_rxp (carb_rst_rnp_@),
                             .carb_rst_rnp (pull_req1));
 
*/

  req test432_gbe5(/*AUTOINST*/);

   req gbe9_vreos(/*AUTOINST*/);


/*  fifo AUTO_TEMPLATE "gbe[0-9]+_\([^\_]+\)" (
                             .clk (@_clk),
                             .\(.*data.*\) (@_\1),
                             .\(.*\)\(full\)\(.*\) (\1@\3),
                             .\(en\|de\)\(.\).+ (@_\1\2));
*/



   fifo #(5)  gbe2_pull_req (/*AUTOINST*/);


  fifo #(5)  
     gbe1_pull_req_fifo( /*AUTOINST*/);
			





   
endmodule // pull_arb
