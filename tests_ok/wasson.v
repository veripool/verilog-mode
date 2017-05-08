`define FOO 1'b1
module foo(__a,b);
   
   input  __a;
   output b;
   
   always @(/*AUTOSENSE*/__a or `FOO) begin
      b = __a ^ `FOO ;
   end
   
endmodule

