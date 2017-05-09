module autoinstparam_belkind (/*AUTOARG*/) ;
   
   parameter X = 8;
   /*
    autoinstparam_belkind_leaf AUTO_TEMPLATE (
    .P (X),
    .a (b[]),
    );
    */
   
   autoinstparam_belkind_leaf (/*AUTOINSTPARAM*/
                               // Parameters
                               .P               (X))             // Templated
     leaf(/*AUTOINST*/
          // Inputs
          .a                            (b[P-1:0]));             // Templated
   
endmodule // tree

// Local Variables:
// eval:(verilog-read-defines)
// eval:(verilog-read-defines "autoinstparam_belkind_leaf.v")
// End:
