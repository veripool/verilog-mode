`timescale 1ns/100ps

module a_h
  #(parameter M=5, N=3)
    ();

   /*AUTOWIRE*/

   autoinst_sv_kulkarni_base
     #(/*AUTOINSTPARAM*/)
     Ia
       (/*AUTOINST*/); // <---- BUG?

endmodule
