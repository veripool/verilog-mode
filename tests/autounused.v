module wbuf
  #(parameter width=1)
  (output [width-1:0] q,
   input [width-1:0]  d);
endmodule

module autounused
  #(parameter width=3)
  (/*AUTOARG*/) ;

   /*AUTOOUTPUT*/
   input    da, db, dc, dd;
   /*AUTOINPUT*/

   wire _unused_ok = &{/*AUTOUNUSED*/
                       1'b0};

   defparam partbuf.width = width;
   wbuf wbuf
     (// Inputs
      .d                                ({da,db,dc}),
      /*AUTOINST*/);

endmodule // abuf

// Local Variables:
// verilog-auto-unused-ignore-regexp: "^db$"
// End:
