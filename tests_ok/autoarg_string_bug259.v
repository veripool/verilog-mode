module bug_minimal
  (input wire GND,
   input wire VDD,
   
   inout wire PIN1,
   inout wire PIN2,
   inout wire PIN3,
   inout wire PIN4
   
   /*AUTOARG*/);
   
   // ----------------------------------------------------------------
   /*AUTOWIRE*/
   
   // ----------------------------------------------------------------
   task force_value_to_1;
      begin
         $display("Enable test module checking ...");
         force `value = 1'b1;
      end
   endtask
   
   // ---------------------------------------------------------------
   task force_value_to_0;
      begin
         $display("Disable test module checking ...");
         force `value = 1'b0;
      end
   endtask
   
endmodule
