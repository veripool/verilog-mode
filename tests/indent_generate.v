module test();

  reg [3:0] x;

  genvar    i;
  generate
  for(i=0; i<4; i=i+1) begin:a
  always @(*) begin
  x[i] = 1;
  end
  wire y = 0;
  end
  endgenerate
endmodule // test


module test();

  reg [3:0] x;

  genvar    i;

  for(i=0; i<4; i=i+1) begin:a
  always @(*) begin
  x[i] = 1;
  end
  wire y = 0;
  end

endmodule // test

