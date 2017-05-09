module wbuf
  #(parameter width=1)
   (output [width-1:0] q,
    input [width-1:0] d);
endmodule

module autounused
  #(parameter width=3)
   (/*AUTOARG*/
    // Outputs
    q,
    // Inputs
    da, db, dc, dd
    ) ;
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [width-1:0] q; // From wbuf of wbuf.v
   // End of automatics
   input              da, db, dc, dd;
   /*AUTOINPUT*/
   
   wire               _unused_ok = &{/*AUTOUNUSED*/
                                     // Beginning of automatic unused inputs
                                     dd,
                                     // End of automatics
                                     1'b0};
   
   defparam partbuf.width = width;
   wbuf wbuf
     (// Inputs
      .d                                ({da,db,dc}),
      /*AUTOINST*/
      // Outputs
      .q                                (q[width-1:0]));
   
endmodule // abuf

// Local Variables:
// verilog-auto-unused-ignore-regexp: "^db$"
// End:
