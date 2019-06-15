module ExampMain
  (input i,
   output o,
   inout  io);
endmodule

module ExampInOutIn (/*AUTOARG*/
                     // Inputs
                     i, io, o
                     );
   /*AUTOINOUTIN("ExampMain")*/
   // Beginning of automatic in/out/inouts (from specific module)
   input i;
   input io;
   input o;
   // End of automatics
endmodule

// Local Variables:
// indent-tabs-mode: nil
// End:
