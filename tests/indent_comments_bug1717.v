// Bug 1717
module test
  (input wire test5 // bla
   /*AUTOARG*/);

`include "bla.vh"

   reg        test4;

   wire       test3;

   //  // FIXXME
              wire       test1 = test2; // wrong indent
   wire                  test = test;

endmodule
