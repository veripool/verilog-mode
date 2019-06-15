`define XX_FOO
`define M_BAR(x)
`define M_BAZ
...
`ifdef NEVER
 `undef M_BAZ  // Emacs will see this and not `undef M_BAZ
`endif
  ...
/*AUTOUNDEF*/
// Beginning of automatic undefs
`undef M_BAR
`undef XX_FOO
// End of automatics

// Local Variables:
// indent-tabs-mode: nil
// End:
