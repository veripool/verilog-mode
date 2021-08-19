module x;
   
   reg [31:0]                                 mb_reg_output;
   
   // 16 registers max, register 15 is always the version number, so 15 are useable
   // NOTE: number_interface_regs must be the maximum (or 16 in this case) to get the version register
   parameter                                  NUMBER_INTERFACE_REGS = 16;
   parameter                                  MB_REG_START = 3; // start at 4th register location 'h0010
   parameter                                  CMD_REG_0_ADDR = MB_REG_START;
   parameter                                  CMD_REG_1_ADDR = MB_REG_START+1;
   parameter                                  CMD_REG_2_ADDR = MB_REG_START+2;
   parameter                                  CMD_REG_3_ADDR = MB_REG_START+3;
   parameter                                  CMD_REG_4_ADDR = MB_REG_START+4;
   parameter                                  CMD_REG_5_ADDR = MB_REG_START+5;
   parameter                                  CMD_REG_6_ADDR = MB_REG_START+6;
   parameter                                  CMD_REG_7_ADDR = MB_REG_START+7;
   parameter                                  CMD_REG_8_ADDR = MB_REG_START+8;
   parameter                                  CMD_REG_9_ADDR = MB_REG_START+9;
   parameter                                  CMD_REG_10_ADDR = MB_REG_START+10;
   // mode regs
   parameter                                  MODE_REG_0_ADDR = CMD_REG_8_ADDR;
   
   // Absolute register 14 is Error counter
   parameter                                  CMD_REG_14_ADDR = 14;
   parameter                                  CRC_ERROR_REG_ADDR = CMD_REG_14_ADDR;
   // ------------ VERSION register is 15
   parameter                                  VERSION_REG_ADDR = 15;
   
   reg [NUMBER_INTERFACE_REGS-1:MB_REG_START] mb_reg_wr;
   reg [NUMBER_INTERFACE_REGS-1:MB_REG_START] mb_reg_rd;
   wire [31:0]                                mb_reg_out_w [NUMBER_INTERFACE_REGS-1:MB_REG_START];
   wire [31:0]                                interface_from_core_fp;
   
   assign
     mb_reg_out_w[VERSION_REG_ADDR] = BUILD_VERSION;
   
   integer mb_loop;
   always @(/*AUTOSENSE*/ /*memory or*/ interface_from_core_fp or mb_reg_rwn or mb_reg_select)
     
     begin: MB_READ_WRITE_SEL_P
        
        mb_reg_wr     = 'h0;
        mb_reg_rd     = 'h0;
        mb_reg_output = interface_from_core_fp;
        
        for(mb_loop = MB_REG_START; mb_loop < NUMBER_INTERFACE_REGS; mb_loop=mb_loop+1)
          begin
             if(mb_reg_select[mb_loop] == 1'b1)
               begin
                  mb_reg_rd[mb_loop] = mb_reg_select[mb_loop] &  mb_reg_rwn;
                  mb_reg_wr[mb_loop] = mb_reg_select[mb_loop] & !mb_reg_rwn;
                  mb_reg_output      = mb_reg_out_w[mb_loop];
               end
          end
     end
endmodule // x
