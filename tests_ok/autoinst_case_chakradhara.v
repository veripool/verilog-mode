module foo();
   /*bar AUTO_TEMPLATE (
    .pme\(.*\)_o             (pme\1[]),
    .PME\(.*\)_o             (pMe\1[]),
    .pme\(.*\)_o             (pme\1[]),
    );
    */
   bar bar
     (/*AUTOINST*/
      // Inputs
      .PME_o                            (pMe),                   // Templated
      .pme_o                            (pme),                   // Templated
      .pmE_o                            (pmE_o));
   
endmodule

module bar
  (/*AUTOARG*/
   // Inputs
   PME_o, pme_o, pmE_o
   );
   
   input PME_o;
   input pme_o;
   input pmE_o;
   
endmodule
