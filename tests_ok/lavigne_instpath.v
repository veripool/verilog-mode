module lavigne_instpath ();
   
   /* lavigne_t1 AUTO_TEMPLATE (
    .a(a1),
    );
    */
   lavigne_t1 m1 (/*AUTOINST*/
                  // Inputs
                  .a                    (a1));                   // Templated
   
   /* lavigne_t2 AUTO_TEMPLATE (
    .b(b2),
    );
    */
   
   lavigne_t2 m2 (/*AUTOINST*/
                  // Inputs
                  .b                    (b2));                   // Templated
   
endmodule

// verilkkkkkkkog-library-directories:("*/")

//(load-file "/usr/local/common/site-lisp/local/verilog-mode.el")

// Local Variables:
// verilog-library-flags:("-y lavigne_instpath/")
// End:
