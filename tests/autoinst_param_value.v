module InstMod ( ins, outs );
   parameter WIDTH;
   output [WIDTH-1:0] ins;
endmodule

module test_top;
   parameter TOP_WIDTH = 3;
   /* AUTO_LISP(defun my-param-range ()
                 (concat "[" vh-TOP_WIDTH ":0]"))*/

   /* InstMod AUTO_TEMPLATE(
        .WIDTH(@"vh-TOP_WIDTH"),
        .ins(ins@"(my-param-range)"),
      ) */

   InstMod mod
    #(/*AUTOINSTPARAM*/
      // Parameters
      .WIDTH                            (3))                     // Templated
    (/*AUTOINST*/
     // Outputs
     .ins                               (ins[3:0]));              // Templated

endmodule

// Local Variables:
// verilog-auto-read-includes:t
// End:
