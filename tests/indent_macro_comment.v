// issue 935 - Incorrect indentation after multi-line `define macro
`ifndef _ABC
  `define _ABC

  `define TEMPA 1

// CORRECT INDENTATION

  `define DEF1 { "a" \
                 , "b" \
                 }

    // Incorrect indentation (v1) after multi-line macro definition above

  `define TEMPB (`TEMPA >= 0 ? 0 : 1)

    // Incorrect indentation (v1) *strangely, not yet affected by the >= chars above*

  `define DEF2 { "a" \
                 , "b" \
                 }

                           // Incorrect indentation (v2) *NOW aligns to the
                           // >= sign in `define TEMPB above (which it should not)
                           // Looks like the multi-line macro definition DEF2
                           // above caused this second version of incorrect
                           // indentation*

  `define TEMPC ((`TEMPA + 1_000_000) >= 0 ? 0 : 1)

    // BACK TO Incorrect indentation (v1)!

  `define DEF3 { "a" \
                 , "b" \
                 }

                           // BACK TO Incorrect indentation (v2)! Surprisingly
                           // the >= sign in `define TEMPC macro did not affect
                           // the indentation this time; but the indentation
                           // returned to (v2) as set by that sign in `define TEMPB
`endif

// Local Variables:
// verilog-indent-ignore-multiline-defines: nil
// End:
