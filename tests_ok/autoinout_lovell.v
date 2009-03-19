// Matthew Lovell <lovell@hp.com>

module top_test(/*AUTOARG*/
                // Outputs
                ba, aa,
                // Inputs
                e, dc, db, da, \c-escaped-vec , \c-escaped-nvec 
                );
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output      aa; // From l1 of leaf.v
   output      ba; // From l1 of leaf.v
   // End of automatics
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input       \c-escaped-nvec ; // To l1 of leaf.v
   input [2:0] \c-escaped-vec ; // To l1 of leaf.v
   input       da; // To l1 of leaf.v
   input [1:0] db; // To l1 of leaf.v
   input [2:0] dc; // To l1 of leaf.v
   input       e;                       // To l1 of leaf.v
   // End of automatics
   
   /* leaf AUTO_TEMPLATE (
    // Original reported bug
    .a  ({aa, test2.test3.no, test3.test4.no2}),
    // Others
    .b  ( ~ ba),
    .c  ({\c-escaped-nvec , \c-escaped-vec [2:0] }),
    .d  ({da,~ db [1:0] , dc [2:0]}),
    );
    */
   leaf l1 (/*AUTOINST*/
            // Outputs
            .a                          ({aa, test2.test3.no, test3.test4.no2}), // Templated
            .b                          ( ~ ba),                 // Templated
            // Inputs
            .c                          ({\c-escaped-nvec , \c-escaped-vec [2:0] }), // Templated
            .d                          ({da,~ db [1:0] , dc [2:0]}), // Templated
            .e                          (e));
endmodule // top_test

module leaf(/*AUTOARG*/
            // Outputs
            a, b,
            // Inputs
            c, d, e
            );
   output a;
   output b;
   input  c;
   input  d;
   input  e;
endmodule
