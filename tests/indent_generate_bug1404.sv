// Bug 1404

module test
  #(paramweter integer OPT = 1
     )
    (input logic y,z;
    );

    if (OPT = 1) begin
       always_comb begin
          y = 1'b1;
       end
end else begin
    always_comb begin
       y = 1'b0;
    end
end

    if (OPT = 1) begin
       assign z = 1'b1;
    end else begin
       assign z = 1'b0;
    end

endmodule // test
