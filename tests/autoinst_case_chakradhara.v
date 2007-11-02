module foo();
   /*bar AUTO_TEMPLATE (
    .pme\(.*\)_o             (pme\1[]),
    .PME\(.*\)_o             (pMe\1[]),
    .pme\(.*\)_o             (pme\1[]),
    );
    */
   bar bar
     (/*AUTOINST*/);

endmodule

module bar
  (/*AUTOARG*/);

   input PME_o;
   input pme_o;
   input pmE_o;

endmodule
