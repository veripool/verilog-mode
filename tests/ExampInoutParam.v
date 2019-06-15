        module ExampMain ();
          parameter PARAM = 22;
        endmodule

        module ExampInoutParam ();
           /*AUTOINOUTPARAM("ExampMain")*/
           // Beginning of automatic parameters (from specific module)
           parameter       PARAM;
           // End of automatics
        endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
