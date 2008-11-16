module foo;
`ifdef LABEL_A
   CHIP CPU (
             .clkin(clkin),
 `ifdef LABEL_B
             .bclko(bclko),
 `endif
             .cmode(cmode),
             );
   input sysclk;
 `ifdef LABEL_B
   input bclko;
 `endif
   input cmode;
`endif

   // instead of:

`ifdef LABEL_A
   CHIP CPU (
             .clkin(clkin),
 `ifdef LABEL_B
             .bclko(bclko),
 `endif
             .cmode(cmode),
             );
   input sysclk;
 `ifdef LABEL_B
   input bclko;
 `endif
   input cmode;
`endif

endmodule // foo
