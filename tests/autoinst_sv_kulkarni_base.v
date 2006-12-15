`timescale 1ns/100ps

// -----------------------------------------------------------------------------
// Leaf module using multi-dimensional array ports
// -----------------------------------------------------------------------------
module autoinst_sv_kulkarni_base
  // Verilog 2001 style
  #(parameter M=5, N=3)
    (
    output logic [N-1:0][M-1:0] a_o1,
    input [N-1:0][M-1:0] a_i1
     );

   // -----------------------------------------------------------------------------
   // Main Code
   always_comb begin
      for (int i=0; i<N; i++)
        a_o1[i] = ^(a_i1[i]);
   end

endmodule
