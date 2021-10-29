module bug(output [7:0] a);
   
   initial begin
      a = 0;
   end
   
   always begin
      # 10;
      a += 1;
   end
endmodule

module top;
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [7:0] a;                       // From bug of bug.v
   // End of automatics
   
   bug bug(/*AUTOINST*/
           // Outputs
           .a                           (a[7:0]));
   
   initial begin
      # 1000;
      if (int'(a) > 5) begin
         $display("Test");
      end
   end
   
endmodule
