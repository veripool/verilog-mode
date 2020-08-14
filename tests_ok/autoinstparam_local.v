//bug889

module leaf #(
              parameter  DATA_WIDTH = 256,
              localparam STRB_WIDTH_SHOULD_BE_HIDDEN = DATA_WIDTH/8 )
   ();
endmodule

module test;
   parameter integer DATA_WIDTH = 256;
   parameter integer STRB_WIDTH = DATA_WIDTH/8;
   
   /* leaf AUTO_TEMPLATE (
    .DATA_WIDTH( DATA_WIDTH ),
    .STRB_WIDTH_SHOULD_BE_HIDDEN ( STRB_WIDTH ),
    .\(.*\) ( \1 ),
    );*/
   
   leaf
     #( /*AUTOINSTPARAM*/
        // Parameters
        .DATA_WIDTH                     ( DATA_WIDTH ))          // Templated
   u_leaf
     ( /*AUTOINST*/);
   
endmodule
