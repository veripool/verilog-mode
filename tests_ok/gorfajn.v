module x;
   always @(/*autosense*/d32S_CurCcbH or ramS_CcbBaseH or ramS_ccbsizeH)
     begin
        case (ramS_ccbsizeH)
          2'b00 : ramS_CcbAddH = {2'b00, d32S_CurCcbH };
          2'b01 : ramS_CcbAddH = {1'b0, d32S_CurCcbH, 1'b0};
          2'b10 : ramS_CcbAddH = {d32S_CurCcbH, 2'b00};
          2'b11 : ramS_CcbAddH = {d32S_CurCcbH, 2'b00}; // unused
        endcase
        ramS_CcbAddresH = {10'h000, ramS_CcbAddH} + ramS_CcbBaseH;
     end
endmodule
