module foo;
   input a,b;
   
   always @(a) begin
      b <= #10 ~ a;
   end
endmodule // foo

module bar;
   // 
   input a,b;
   
   always @(a) begin // 
      b <= #10 ~  a;

      a;
   end
endmodule // foo
