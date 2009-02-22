module autowire_long_yaohung(/*AUTOARG*/
                             // Outputs
                             data_out
                             );
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [`LONGNAMELONGNAMELONGNAMELONGNAMELONGNAMELONGNAME] data_out;// From top of top.v
   // End of automatics
   /*AUTOWIRE*/
   /*AUTOREG*/
   
   top top
     (/*AUTOINST*/
      // Outputs
      .data_out                         (data_out[`LONGNAMELONGNAMELONGNAMELONGNAMELONGNAMELONGNAME]));
   
endmodule

module top(/*AUTOARG*/
           // Outputs
           data_out
           );
   
   output [`LONGNAMELONGNAMELONGNAMELONGNAMELONGNAMELONGNAME] data_out;
   
endmodule
