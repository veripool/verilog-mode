module foo();
   parameter test = 0;
   
   

   genvar    i,j;
   
   /* bar AUTO_TEMPLATE (
    .o   (o[i]),
    .i   (i[i]),
    ); */
   for(i=0;i<3;i=i+1) begin

      bar I_BAR
        (/*AUTOINST*/
         // Outputs
         .o                            (o[i]),                  // Templated
         // Inputs
         .i                            (i[i]));                         // Templated
      // ^- new port indent
      //   ^- old indent
   end

   /* bar AUTO_TEMPLATE (
    .o   (o[j]),
    .i   (i[j]),
    ); */
   
   generate
      if (test == 1) begin : TEST
         for ( j = 0 ; j < 2 ; j = j + 1) begin
            bar I_BAR_TEST
              (/*AUTOINST*/
               // Outputs
               .o                  (o[j]),                  // Templated
               // Inputs
               .i                  (i[j]));                         // Templated
            // ^- new port indent
            //      ^- old port indent
         end
      end
   endgenerate

   for (genvar k = 0; k < 4; k=k+1) begin
      /* bar AUTO_TEMPLATE (
       .o   (o[k]),
       .i   (i[k]),
       ); */
      
      bar I_BAR_TEST
        (/*AUTOINST*/
         // Outputs
         .o                  (o[j]),                  // Templated
         // Inputs
         .i                  (i[j]));                         // Templated
      // ^- new port indent
      //            ^- old port indent
   end
   
   /* bar AUTO_TEMPLATE (
    .o   (o[long_var]),
    .i   (i[long_var]),
    ); */
   
   generate
      for ( genvar long_varj = 0 ; j < 2 ; j = j + 1) begin
         bar I_BAR_LONG
           (/*AUTOINST*/
            // Outputs
            .o                      (o[long_var]),           // Templated
            // Inputs
            .i                      (i[long_var]));          // Templated
         // ^- new port indent
         //                     ^- old port indent
      end
   end
endgenerate

   logic bob, sub, lob, fob, rob, sod;

   always_comb begin
      bob = sub | ( lob &
                    fob) |
            rob ^
            sod;
      //    ^sod    ^fob - indenting due to assign and parenthesis
   end
   
   
endmodule // foo

module bar
  (output o,
   input i);
   o=i;
   
endmodule
