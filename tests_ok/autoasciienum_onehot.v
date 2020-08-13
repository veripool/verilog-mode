// lint_checking MODLNM OFF

module autoasciienum_onehot (
                             input  clk,
                             input  rst_n,
                             output ack
                             );
   
   localparam // synopsys enum state_info
              IDLE = 0,
              S1 = 1,
              S2 = 2,
              S3 = 3,
              DONE = 4;
   
   reg [4:0]  // synopsys enum state_info
              cur_state, nxt_state;
   
   always @ (*) begin
      nxt_state = 5'h0;
      
      case (1'b1)
        cur_state[IDLE] : nxt_state[S1]   = 1'b1;
        cur_state[S1]   : nxt_state[S2]   = 1'b1;
        cur_state[S2]   : nxt_state[S3]   = 1'b1;
        cur_state[S3]   : nxt_state[DONE] = 1'b1;
        cur_state[DONE] : nxt_state[DONE] = 1'b1;
      endcase
   end
   
   always @ (posedge clk or negedge rst_n)
     if (rst_n == 1'b0) begin
        cur_state <= 'h1;
     end
     else begin
        cur_state <= nxt_state;
     end
   
   assign ack = cur_state[DONE];
   
   /*AUTOASCIIENUM("cur_state", "cur_state_ascii")*/
   // Beginning of automatic ASCII enum decoding
   reg [31:0] cur_state_ascii;  // Decode of cur_state
   always @(cur_state) begin
      case ({cur_state})
        (5'b1<<IDLE):     cur_state_ascii = "idle";
        (5'b1<<S1):       cur_state_ascii = "s1  ";
        (5'b1<<S2):       cur_state_ascii = "s2  ";
        (5'b1<<S3):       cur_state_ascii = "s3  ";
        (5'b1<<DONE):     cur_state_ascii = "done";
        default:          cur_state_ascii = "%Err";
      endcase
   end
   // End of automatics
   
endmodule
