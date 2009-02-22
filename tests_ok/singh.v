// HERE IS THE TEST CASE
module bt (/*AUTOARG*/
           // Outputs
           out,
           // Inputs
           in
           );
   input [7:0]  in;
   output [7:0] out;
   
   wire [7:0]   out = ~in;
endmodule // bottm

module top (/*AUTOARG*/
            // Outputs
            outgo,
            // Inputs
            incom
            );
   input [31:0]  incom;
   output [31:0] outgo;
   
   /* bt  AUTO_TEMPLATE (
    .in (incom[@"(+ (* 8 @) 7)":@"(* 8 @)"]),
    .out (outgo[@"(concat (int-to-string (+ (* 8 @) 7)) \":\" (int-to-string ( * 8 @)))"]));
    */
   
   bt BT0 (/*AUTOINST*/
           // Outputs
           .out                         (outgo[7:0]),            // Templated
           // Inputs
           .in                          (incom[7:0]));           // Templated
   bt BT1 (/*AUTOINST*/
           // Outputs
           .out                         (outgo[15:8]),           // Templated
           // Inputs
           .in                          (incom[15:8]));          // Templated
   bt BT2 (/*AUTOINST*/
           // Outputs
           .out                         (outgo[23:16]),          // Templated
           // Inputs
           .in                          (incom[23:16]));                 // Templated
   bt BT3 (/*AUTOINST*/
           // Outputs
           .out                         (outgo[31:24]),          // Templated
           // Inputs
           .in                          (incom[31:24]));                 // Templated
   
endmodule // top



