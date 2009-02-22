
covergroup CB;
   a: coverpoint tr.a
     {
      bins a0 = {0};
      bins a1 = {1};
      option.weight=0;
   }
   b: coverpoint tr.b {
      bins b0 = {0};
      bins b1 = {1};
      option.weight=0;
   }
   ab: cross a,b {
      bins a0b0 = binsof(a.a0) && binsof(b.b0);
      bins a1b0 = binsof(a.a1) && binsof(b.b0);
      bins b0 = binsof(b.b0);
   }
endgroup // CB

