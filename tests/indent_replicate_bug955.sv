// Issue #955

module test (input a, input b, output c);
        parameter s = 4;
        reg [s:0] myreg;
        always @(posedge a) begin
               if (b) begin
                  r <= {s{1'b0}};
               end // <-- this end will be improperly indented unless
            // 's' is replaced with e.g. 4
        end
end
