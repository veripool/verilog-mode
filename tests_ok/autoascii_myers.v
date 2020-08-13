module testit;
   reg             clk;
   reg             a_i;
   reg             b_i;
   
   reg             a_o;
   reg             b_o;
   reg             rst_n;
   
   reg [7:0]       shreg;
   
   
   //== State enumeration
   parameter [2:0] // synopsys enum state_info
                   SM_IDLE = 3'b000,
                   SM_SEND = 3'b001,
                   SM_WAIT1 = 3'b010;
   //== State variables
   reg [2:0]       /* synopsys enum state_info */
                   state_r; /* synopsys state_vector state_r */
   reg [2:0]       /* synopsys enum state_info */
                   state_e1;
   
   //== ASCII state decoding
   
   /*AUTOASCIIENUM("state_r", "_stateascii_r", "sm_")*/
   // Beginning of automatic ASCII enum decoding
   reg [39:0]      _stateascii_r;               // Decode of state_r
   always @(state_r) begin
      case ({state_r})
        SM_IDLE:  _stateascii_r = "idle ";
        SM_SEND:  _stateascii_r = "send ";
        SM_WAIT1: _stateascii_r = "wait1";
        default:  _stateascii_r = "%Erro";
      endcase
   end
   // End of automatics
   
   initial begin
      clk       = 0;
      a_i       = 0;
      b_i       = 0;
      rst_n     = 0;
      #20 rst_n = 1;
   end
   always #5 clk = ~clk;
   
   always @(posedge clk or rst_n) begin
      if (~rst_n) begin
         a_o   <= 0;
         b_o   <= 0;
         shreg <= 8'b00110011;
      end
      else begin
         a_o   <= a_i;
         b_o   <= b_i;
         shreg <= {shreg[6:0], shreg[7]};
      end
   end
   
   task set_a_i;
      begin
         a_i = shreg[0];
      end
   endtask // set_a_i
   
   always @(shreg & a_o) begin
      set_a_i;
   end
   
   initial begin
      $vcdpluson;
      #500 $finish;
   end
   
endmodule // testit
