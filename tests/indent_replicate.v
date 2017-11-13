// Issue #1237 -- "end" not indented correctly after replication with variable number
module test;

   initial begin
      string in_str;

      if (in_str == "") begin : empty_string
     a_string = { 5 {" "}};  // all spaces
      end // block: empty_string
   end // initial begin

   initial begin
      string in_str;
      int    width = 5;

      if (in_str == "") begin : empty_string
     a_string = { width {" "}};  // all spaces
   end // block: empty_string
   end // initial begin

   function string a_string (string in_str);
      if (in_str == "") begin : empty_string
     a_string = { width {" "}};  // all spaces
   end // block: empty_string
      endfunction // a_string

endmodule // test
