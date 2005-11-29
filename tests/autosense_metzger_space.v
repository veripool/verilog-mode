module x (/*AUTOARG*/
   // Outputs
   rmsk0, rmsk1, rmsk2,
   // Inputs
   endbyte0, endbyte1, endbyte2, strtbyte0, strtbyte1, strtbyte2
   );
   input endbyte0;
   input endbyte1;
   input endbyte2;
   input strtbyte0;
   input strtbyte1;
   input strtbyte2;
   output rmsk0;
   output rmsk1;
   output rmsk2;

   always @ (/*AS*/endbyte0 or strtbyte0) rmsk0 = maskcalc(strtbyte0,endbyte0);
   always @ (/*AS*/endbyte1 or strtbyte1) rmsk1 = maskcalc(strtbyte1,endbyte1);
   always @ (/*AS*/endbyte2 or strtbyte2) rmsk2 = maskcalc(strtbyte2,endbyte2);

endmodule
