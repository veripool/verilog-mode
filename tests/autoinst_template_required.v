// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.

module autoinst_multitemplate ();

   /*
     SubB AUTO_TEMPLATE (
     .b (Boo@),
     .other (Other),
    );*/

   SubB subb (/*AUTOINST*/
              // Inputs
              .b                        (Boo),                   // Templated
              .other                    (Other));                // Templated

   SubC subc (/*AUTOINST*/);

endmodule

module SubB (input not_listed, input b, input other);
endmodule

module SubC (input also_not_listed, input b);
endmodule

// Local Variables:
// verilog-auto-inst-template-required: t
// End:
