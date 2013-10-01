//bug284

module wrapper
 (
  /*AUTOOUTPUT*/
  /*AUTOINPUT*/
  );

 //--------------------------------------------------------------------------

 // Note input/output comments aren't needed, and multiple signals
 // per line are ok
 or u_or [31:0]
   (o[31:0], i0[31:0], i1[31:0], i2[31:0],
    // Inputs,
    i3[31:0]
    /*AUTOINST*/);

// bug676
 buf # 1 mybuf[1:0]
   (bout[1:0],
    // Inputs,
    bin[1:0]
    /*AUTOINST*/);

 //--------------------------------------------------------------------------

endmodule
