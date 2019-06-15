module InstModule (o,i);
   parameter PAR;
endmodule

module ExampInstParam (o,i);
   parameter PAR;
   InstModule #(/*AUTOINSTPARAM*/
                // Parameters
                .PAR            (PAR))
   instName (/*AUTOINST*/);
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
