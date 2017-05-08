module x;
   
   always @(/*AUTOSENSE*/arb_select_f or octet_idx) begin
      octet_flag[0]   = |arb_select_f[ 7: 0];
      octet_flag[1]   = |arb_select_f[15: 8];
      octet_flag[2]   = |arb_select_f[23:16];
      octet_flag[3]   = |arb_select_f[31:24];
      octet_flag[4]   = |arb_select_f[39:32];
      octet_flag[5]   = |arb_select_f[47:40];
      octet_flag[6]   = |arb_select_f[55:48];
      octet_flag[7]   = |arb_select_f[63:56];
      
      octet_available = |octet_flag;
      
      shifted8_64     = barrel_shifter(octet_flag, octet_idx[5:3]);
   end // always @ (arb_select_f)
   
endmodule

function [7:0] barrel_shifter;
   
   input [7:0] source;
   input [2:0] shift_amt;
   
   begin
      case (shift_amt) //synopsys parallel_case full_case
        3'b0: barrel_shifter = source;
        3'b1: barrel_shifter = {source[0], source[7:1]};
        3'b2: barrel_shifter = {source[1:0], source[7:2]};
        3'b3: barrel_shifter = {source[2:0], source[7:3]};
        3'b4: barrel_shifter = {source[3:0], source[7:4]};
        3'b5: barrel_shifter = {source[4:0], source[7:5]};
        3'b6: barrel_shifter = {source[5:0], source[7:6]};
        3'b7: barrel_shifter = {source[6:0], source[7]};
      endcase // case(shift_amt)
   end
   
endfunction // barrel_shifter

