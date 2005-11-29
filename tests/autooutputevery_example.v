module ex_output_every (o,i,tempa,tempb)
  output o;
   input i;

   /*AUTOOUTPUTEVERY*/
   // Beginning of automatic outputs (every signal)
   output		tempa;
   output		tempb;
   // End of automatics

   wire  tempa = i;
   wire  tempb = tempa;
   wire  o = tempb;

endmodule
