module t_autoinst_def_clk
   (/*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input		a,			// To sub of sub.v
   input		b,			// To sub of sub.v
   input		clk,			// To sub of sub.v
   // End of automatics

    /*AUTOOUTPUT*/
    // Beginning of automatic outputs (from unused autoinst outputs)
    output		c			// From sub of sub.v
    // End of automatics
    );

   sub sub
      (/*AUTOINST*/
       // Outputs
       .c				(c),
       // Inputs
       .clk				(clk),
       .a				(a),
       .b				(b));

endmodule // sdc_wombat

module sub
   (input clk,

    input a,
    input b,

    output c
    );

   clocking cb
     @(posedge clk);
   endclocking

   default clocking cb;

endmodule
