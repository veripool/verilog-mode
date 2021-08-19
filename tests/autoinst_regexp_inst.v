module sub;
   parameter AA, AB, AC;
   output ia, ib, ic;
endmodule

module autoinst_regexp_inst;

   /*AUTOWIRE*/

   // We don't yet support AUTO INST with a parameter

   sub
     #(/*AUTOINSTPARAM("AB")*/)
   sub0
     (/*AUTOINST*/);

   sub
   sub1
     (/*AUTOINST("ia")*/);

   sub
   sub1
     (/*AUTOINST("?!ia")*/);

endmodule
