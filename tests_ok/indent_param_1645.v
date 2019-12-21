module test();
   submodule #(
     .param1("HI"),
     // Pre-fix, attempting to indent here yielded
     // Scan error: "Unbalanced parenthesis", 50, 1
     ) modname ();
endmodule

// Local Variables:
// verilog-indent-lists: nil
// End:
