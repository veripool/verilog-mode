        module ExampReg (o,i);
           output o;
           input i;
           /*AUTOREG*/
           // Beginning of automatic regs (for this module's undeclared outputs)
           reg             o;
           // End of automatics
           always o = i;
        endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
