
module sm ();

   localparam STATES = 7;

   localparam /* synopsys enum states */
     IDLE         = 0, // '001
     READ         = 1, // '002
     THINK        = 2, // '004
     SEND         = 3, // '008
     WAIT         = 4, // '040
     GET_ACK      = 5, // '080
     WAIT_REGBUS  = 6; // '100
   
   reg [STATES-1:0] /*synopsys enum states*/
             state_i, state_r; /* synopsys state_vector state_r */
   
   /*AUTOASCIIENUM("state_r","state_onehot,ascii_r","","onehot")*/

   /*AUTOASCIIENUM("state_r","state_notonehot_ascii_r")*/

endmodule
