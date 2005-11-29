module ex_output_every (o,i,tempa,tempb)
  output o;
   input i;

   /*AUTOOUTPUTEVERY*/
   // Beginning of automatic outputs (every signal)
   output		tempa;
   output		tempb;
   // End of automatics

   wire  tempa;
   wire  tempb;
   wire  o;

   assign tempa = i;
   assign tempb = tempa;
   assign o = tempb;
endmodule
