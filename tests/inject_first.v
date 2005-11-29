module ex_inject (i, o);
   input i;
   input j;
   output o;

   // Ok:
   always @ (j or i)
     o = i | j;
   // No change:
   always @ (j) o = i | j;
   always @ (j or i or p) o = i | j;
   // Instant

   autoinst_lopaz_srpad pad
     (.pin(pin),
      .foo(bar),
      .clk(newclk));

endmodule
