module test();

  // function with no lifetime, return-type, or port-list
  function f0;
    blah0;
  endfunction

  // empty port-list
  function f1();
    blah1;
  endfunction

  // non-empty portlist
  function f2(stuff2);
    blah2;
  endfunction

  // test that ": function_identifier" remains unscathed
  function f3;
  endfunction : f3

  // return type
  function void f4;
    blah4;
  endfunction

  // return type with empty port-list.
  function void f5();
    int i;
    begin
      blah4;
    end
  endfunction

  // return type, non-empty portlist
  // also check that a stale auto-comment gets removed
  function void f6(stuff,
                   that,
                   spans,
                   lines);
    blah5;
  endfunction // fX

  // test lifetime keywords 'automatic' and 'static'
  function automatic f7();
  endfunction

  // test a crazy-long function declaration
  function static union packed signed {bit[1:0] a, bit[2:0] b} [5:0] f8(input ports, input ports, output ports);
  endfunction

  // port-list that doesn't start on the same line as the function declaration
  function automatic void f9
    (int a,
     int b);
  endfunction

  // mismatched keyword
  function f10;
  endtask

  // make sure previous screw-up doesn't affect future functions
  function f11;
  endfunction

endmodule
