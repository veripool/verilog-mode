module example(out1, out2, out3);
   (* LOC = "D14" *)
   output out1;
   /* foobar */ (* LOC = "C15" *) /* jar */ output out2;
   (* LOC = "C16" *)
   output out3;
   out1 = 1'b1;
   out2 = 1'b1;
   out3 = 1'b1;
endmodule
