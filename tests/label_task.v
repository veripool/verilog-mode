module test();

  // task with no lifetime, return-type, or port-list
  task t0;
    blah0;
  endtask

  // empty port-list
  task t1();
    blah1;
  endtask

  // non-empty portlist
  task t2(stuff2);
    blah2;
  endtask

  // test that ": task_identifier" remains unscathed
  task t3;
  endtask : t3

  // check that stale auto-label is overwritten
  task t4(input port1, output port2, inout port3);
    begin
      blah blah blah;
    end
  endtask // tX

  // test lifetime keywords 'automatic' and 'static'
  task static t7();
  endtask

  // test a more complete example
  task automatic  t8(input ports, input ports, output ports);
  endtask

  // port-list that doesn't start on the same line as the task declaration
  task automatic t9
    (int a,
     int b);
  endtask

  // mismatched keyword
  task t10;
  endfunction

  // make sure even the simplest test works after all the insanity
  task t11;
  endtask

endmodule
