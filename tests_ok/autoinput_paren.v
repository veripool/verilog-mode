module foo (/*AUTOARG*/
            // Inputs
            abd, abc
            ) ;
   /*AUTOINPUT("ab\(c\|d\)")*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input abc; // To i_bar of bar.v
   input abd;                   // To i_bar of bar.v
   // End of automatics
   bar i_bar(/*AUTOINST*/
             // Outputs
             .aaa                       (aaa),
             // Inputs
             .abc                       (abc),
             .abd                       (abd),
             .bca                       (bca));
   
endmodule // foo

module bar (/*AUTOARG*/
            // Outputs
            aaa,
            // Inputs
            abc, abd, bca
            ) ;
   input  abc,abd,bca;
   output aaa;
endmodule // bar
