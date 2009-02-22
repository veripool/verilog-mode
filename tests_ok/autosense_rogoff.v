
module x;
   always @ (/*as*/a or ff)
     case (a)
       1: if (ff[3:0] == 4'd3)
         sadfsdff;
     endcase
   
   
endmodule
