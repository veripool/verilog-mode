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
`endif //  `ifdef LABEL_A
   reg 	 a,b;
`ifdef A
   always @(a) begin
      b = a; // asfSDfsdfsasa
      b = a; // asfSDfsdfsasa
      b = a; // asfSDfsdfsasa      //
      b = a; // asfSDfsdfsasa      //       
      b = a; // asfSDfsdfsasa      //
      b = a; // asfSDfsdfsasa      //       
      b = a; // asfSDfsdfsasa      //       
      b = a; // asfSDfsdfsasa      //       
      b = a; // asfSDfsdfsasa      //       
   end
`elsif B
   always @(b) begin
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa      //       
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa      //       
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa      //       
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa
      a = b; // asfSDfsdfsasa      //       
   end
`else // !`elsif B
   always @(a or b) begin
      a <= b;
      b <= a;
   end
`endif // !`elsif B
   
   
endmodule // foo
