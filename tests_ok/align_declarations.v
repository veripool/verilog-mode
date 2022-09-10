module foo (
            input logic        in,
            output logic       out,
            input custom_t     my_type,
            input [3:0] byte_t my_word_array_packed,
            output other_t     other_type_array_unpacked [3],
            input custom_e     my_enum,
            output custom_s    my_struct,
            custom_if          my_if
            );
   
   custom_vif my_vif;
   logic      sig1;
   logic      sig2;
   custom_t   my_type1;
   other_t    other_type1;
   custom_if  my_if1;
   
endmodule

// Local Variables:
// verilog-align-typedef-regexp: "\\<[a-zA-Z_][a-zA-Z_0-9]*_\\(t\\|e\\|s\\|if\\|vif\\)\\>"
// End:
