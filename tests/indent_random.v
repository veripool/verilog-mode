module top;
   initial begin
      // Test
      $display("Hello world");
      void'(std::randomize(foo) with {foo < 10;}; );
   end
endmodule // top
/*
      --------------------------
 
It also appears to have indentation problems with the following variation:
 
== The code: ==
*/ 
module top;
   
   initial begin
      // Test
      $display("Hello world");
      assert(std::randomize(foo) with {foo < 10;}; )
	else $error("ERROR randomizing foo");
   end
endmodule // top
/*
 
------------------------------
 
Also tried the following (removed semicolon after closing-curly-brace), and got same result:
*/
 
module top;
   
   initial begin
      // Test
      $display("Hello world");
      void'(std::randomize(foo) with {foo < 10;} );
   end
endmodule // top
