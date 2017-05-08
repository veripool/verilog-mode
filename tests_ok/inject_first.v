module ex_inject (i, o,/*AUTOARG*/
                  // Inputs
                  j
                  );
   input  i;
   input  j;
   output o;
   
   // Ok:
   always @ (/*AS*/i or j)
     o            = i | j;
   // No change:
   always @ (j) o = i | j;
   always @ (j or i or p) o = i | j;
   // Instant
   
   autoinst_lopaz_srpad pad
     (.foo(bar),
      .clk(newclk),
      /*AUTOINST*/
      // Outputs
      .pin_in                           (pin_in[2*w-1:0]),
      // Inouts
      .pin                              (pin[w-1:0]),
      // Inputs
      .pin_out                          (pin_out[w-1:0]),
      .pin_outen                        (pin_outen));
   
endmodule
