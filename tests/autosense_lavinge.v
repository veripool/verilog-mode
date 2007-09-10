module test
  #(parameter FOO=1)
    ( a, b );
input a;
input b;

reg   c;
wire  d;

always @(/*AUTOSENSE*/)
  begin
     c=0;
     if (d) c = b;
  end
endmodule
