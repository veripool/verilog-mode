module xyz
  #(parameter int FOO=1)
   ( input x, output y); 
endmodule 

module pdq;
   input x; output y;
   parameter int FOO=1;
endmodule 

module abc; 
   xyz XYZ
     #(/*AUTOINSTPARAM*/
       // Parameters
       .FOO				(FOO))
   (/*AUTOINST*/
    // Outputs
    .y					(y),
    // Inputs
    .x					(x)); 
   pdq PDQ
     #(/*AUTOINSTPARAM*/
       // Parameters
       .FOO				(FOO))
   (/*AUTOINST*/
    // Outputs
    .y					(y),
    // Inputs
    .x					(x)); 
endmodule 
