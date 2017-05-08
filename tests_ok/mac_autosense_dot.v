//From: Michael McNamara <mac@verilog.com>
//Date: Tue, 27 Jun 2000 04:38:32 -0700 (PDT)
module x;
   
   always @ (/*AS*/top.agc_tool.adc_dta_i or top.agc_tool.adc_preagc_dta_i) begin
      agctoolerr = top.agc_tool.adc_dta_i / top.agc_tool.adc_preagc_dta_i;
   end
   
endmodule
