module x;
   
   always @ (/*AS*/a or b or c)
     if (a) q = b;
   else r = c;
   
   always @ (/*AS*/a or b or c or d or e)
     if (a) q = b;
   else if (c) r = d;
   /* skip comments as usual */
   else r = e;
   
endmodule
