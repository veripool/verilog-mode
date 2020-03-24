module test();
   
   // function with no lifetime, return-type, or port-list
   function f0;
      blah0;
   endfunction // f0
   
   // empty port-list
   function f1();
      blah1;
   endfunction // f1
   
   // non-empty portlist
   function f2(stuff2);
      blah2;
   endfunction // f2
   
   // test that ": function_identifier" remains unscathed
   function f3;
   endfunction : f3
   
   // return type
   function void f4;
      blah4;
   endfunction // f4
   
   // return type with empty port-list.
   function void f5();
      int i;
      begin
         blah4;
      end
   endfunction // f5
   
   // return type, non-empty portlist
   // also check that a stale auto-comment gets removed
   function void f6(stuff,
                    that,
                    spans,
                    lines);
      blah5;
   endfunction // f6
   
   // test lifetime keywords 'automatic' and 'static'
   function automatic f7();
   endfunction // f7
   
   // test a crazy-long function declaration
   function static union packed signed {bit[1:0] a, bit[2:0] b} [5:0] f8(input ports, input ports, output ports);
   endfunction // f8
   
   // port-list that doesn't start on the same line as the function declaration
   function automatic void f9
     (int a,
      int b);
   endfunction // f9
   
   // mismatched keyword
   function f10;
   endtask // unmatched end(function|task|module|connectmodule|primitive|interface|package|class|clocking)

// make sure previous screw-up doesn't affect future functions
function f11;
endfunction // f11

endmodule // test
