module autosense_inandout(a,b);
   
   input  a;
   output b;
   reg    b;
   reg    c;
   
   always @(/*AUTOSENSE*/a) begin
      c=a;
      b=c;
   end
   
endmodule

