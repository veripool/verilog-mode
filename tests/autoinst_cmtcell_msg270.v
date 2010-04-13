module ex;

   subwidth u_a2	// commented
     (/*AUTOINST*/
      // Outputs
      .bus4a				(bus4a[0:3]));

endmodule

module subwidth (/*AUTOARG*/
   // Outputs
   bus4a
   );
   output [0:3] bus4a;
endmodule
