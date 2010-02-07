module foo(input bit [3:0] def,
           input bit       ghi,
           input bit [1:0] jkl);
   
   task cba(input bit [3:0] a,
            input b,
            c);
   endtask // cba
   task abc(input bit [3:0] def,
            input bit       ghi,
            input bit [1:0] jkl);
      
   endtask // abc
endmodule // foo
