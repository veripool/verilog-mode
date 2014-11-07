module test();
   
   // task with no lifetime, return-type, or port-list
   task t0;
      blah0;
   endtask // t0
   
   // empty port-list
   task t1();
      blah1;
   endtask // t1
   
   // non-empty portlist
   task t2(stuff2);
      blah2;
   endtask // t2
   
   // test that ": task_identifier" remains unscathed
   task t3;
   endtask : t3
   
   // check that stale auto-label is overwritten
   task t4(input port1, output port2, inout port3);
      begin
         blah blah blah;
      end
   endtask // t4
   
   // test lifetime keywords 'automatic' and 'static'
   task static t7();
   endtask // t7
   
   // test a more complete example
   task automatic  t8(input ports, input ports, output ports);
   endtask // t8
   
   // port-list that doesn't start on the same line as the task declaration
   task automatic t9
     (int a,
      int b);
   endtask // t9
   
   // mismatched keyword
   task t10;
   endfunction // unmatched end(function|task|module|primitive|interface|package|class|clocking)

// make sure even the simplest test works after all the insanity
task t11;
endtask // t11

endmodule // test
