// bug637

module submod_a
  (
   //Inputs
   input wire signed [15:0]  serial_in,
   //Outputs
   output wire signed [15:0] parallel_out [0:7]
   );
endmodule

module submod_b
  (
   //Inputs
   input wire signed [15:0]  parallel_out [0:7],
   //Outputs
   output wire signed [15:0] final_out [0:7]
   );
endmodule

module top
  (
   /*AUTOINPUT*/
   /*AUTOOUTPUT*/
   );

   /*AUTOLOGIC*/

   submod_a a_inst
     (/*AUTOINST*/);

    submod_b b_inst
      (/*AUTOINST*/);

    
endmodule
