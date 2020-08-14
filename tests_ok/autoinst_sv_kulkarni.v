`timescale 1ns/100ps

// -----------------------------------------------------------------------------
// One-level up Hierarchical module
// -----------------------------------------------------------------------------
module a_h
  // Verilog 2001 style
  #(parameter M=5, N=3)
   (
    // Outputs
    output [N-1:0] [M-1:0] a_o1         // From Ia of autoinst_sv_kulkarni_base.v
    // End of automatics
    // AUTOINPUT*/
    );
   
   /*AUTOWIRE*/
   
   autoinst_sv_kulkarni_base
     #(/*AUTOINSTPARAM*/
       // Parameters
       .M                               (M),
       .N                               (N))
   Ia
     (/*AUTOINST*/
      // Outputs
      .a_o1                             (a_o1/*[N-1:0][M-1:0]*/),
      // Inputs
      .a_i1                             (a_i1/*[N-1:0][M-1:0]*/)); // <---- BUG?
   
endmodule

// -----------------------------------------------------------------------------
// Top-level module or Testbench
// -----------------------------------------------------------------------------
module top;
   parameter            M=4;
   parameter            N=2;
   
   wire [N-1:0]         a_o1;
   logic [N-1:0][M-1:0] a_i1;
   
   logic                temp;
   
   /*AUTOWIRE*/
   
   // Workaround to fix multi-dimensional port problem
   // a) Set "verilog-auto-inst-vector = nil"
   // b)  ----> a_h AUTO_TEMPLATE ( .\(.*\)   (\1), ); */
   
   a_h #(/*AUTOINSTPARAM*/
         // Parameters
         .M                             (M),
         .N                             (N))
   Ua_h
     (/*AUTOINST*/
      // Outputs
      .a_o1                             (a_o1/*[N-1:0][M-1:0]*/));    // <---- BUG?
   
   // Stimulus
   initial begin
      a_i1 = { 4'h0, 4'h2 };
      #5;
      $display("Loop Init: a_i1 = { %h, %h }   a_o1 = %h\n",
               a_i1[1], a_i1[0], a_o1);
      #5;
      for (int i=0; i<1; i++) begin
         for (int j=0; j<N; j++) begin
            temp = 1'b0;
            for (int k=0; k<M; k++) begin
               a_i1[j][k] = temp;
               temp       = ~temp;
            end
         end
         #5;
         $display("Loop %0d: a_i1 = { %h, %h }   a_o1 = %h\n",
                  i, a_i1[1], a_i1[0], a_o1);
         #5;
      end
   end
   
endmodule
