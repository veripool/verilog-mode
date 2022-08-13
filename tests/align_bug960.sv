// Issue #960

module img_cnt(
               logic clk,
               logic rst,
               logic frame_vld,
               logic line_vld,
               logic data_vld
               );

   // Expect to restart the alignment from here
   int unsigned      frame_cnt = 0;
   int unsigned      line_cnt = 0;
   int unsigned      data_cnt = 0;

endmodule
