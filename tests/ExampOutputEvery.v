        module ExampOutputEvery (
           /*AUTOOUTPUTEVERY*/
           // Beginning of automatic outputs (every signal)
           output          o,
           output          tempa,
           output          tempb,
           // End of automatics
           input i
           );
           wire tempa = i;
           wire tempb = tempa;
           wire o = tempb;
        endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
