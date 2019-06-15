module ExampInject (i, o,/*AUTOARG*/
                    // Inputs
                    j
                    );
   input  i;
   input  j;
   output o;
   always @ (/*AS*/i or j)
     o = i | j;
   InstModule instName
     (.foobar(baz),
      /*AUTOINST*/
      // Outputs
      .j                         (j));
endmodule

module InstModule (output j/*AUTOARG*/);
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
