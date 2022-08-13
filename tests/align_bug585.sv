// Issue #585

module bug585;
parameter ABC = 1;
parameter integer ABC = 1;
endmodule

module bug585_ext;
parameter ABC = 1;
parameter integer ABCD = 1;
parameter logic [3:0] ABCDE = 4'hF;
localparam ABCDEF = 1;
localparam logic [15:0] ABCDEFG = 16'hFACE;
endmodule
