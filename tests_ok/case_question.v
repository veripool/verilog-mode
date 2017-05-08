module test ();
   
   always @(/*AUTOSENSE*/xyz)
     begin
        casex (xyz)
          4'b???0: r = 1;
          4'b??01: r = 2;
          4'b?001: r = 3;
          default: r = 4;
        endcase
     end
   
   assign x = y;
   
endmodule

