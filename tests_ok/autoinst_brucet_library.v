module andcell (/*AUTOARG*/
                // Outputs
                c,
                // Inputs
                a, b
                );
   
   input  a;
   input  b;
   output c;
   wire   c = a&b;
endmodule

module nandcell (/*AUTOARG*/
                 // Outputs
                 c,
                 // Inputs
                 a, b
                 );
   
   input  a;
   input  b;
   output c;
   wire   c = !(a&b);
endmodule

module orcell (/*AUTOARG*/
               // Outputs
               c,
               // Inputs
               a, b
               );
   
   input  a;
   input  b;
   output c;
   wire   c = a|b;
endmodule
