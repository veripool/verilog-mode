// Issue #1257

module t1
 (
 );

genvar pipe;
logic [1:0] v;
logic x;

//generate
for (pipe=0; pipe<2; pipe++) begin : v_bl
     always_comb begin
         assign v[pipe] = '0;
     end
     assign x = '0;  // will be incorrectly indented to column 0
end
//endgenerate

endmodule




module indent;

    // CASE 1 indented wrong.  See end of module
    for (genvar aa = 0; aa < FF; aa++) begin : gen_hh
       for (genvar bb = 0; bb < FF; bb++) begin : gen_ii
          if (`asdf [aa]) begin : gen_jj

             always_ff @ (negedge cc [aa][bb]) begin
                if (dd [aa][bb])) begin
                   for (uint_t d_idx = 0; d_idx < 16; d_idx++)
                     ee [aa][bb].push_front (tx_dfe_out [aa][bb]  [15 - d_idx]);
                end
             end

    always_ff @ (posedge hs_clk) begin
       ee_size [aa][bb] = ee [aa][bb].size();
       if (ee_size [aa][bb] > 0)
         gg [aa][bb] <= ee [aa][bb].pop_front;
    end

end : gen_jj
       end : gen_ii
    end : gen_hh



    // this indents correctly without generate/endgenerate
    for (genvar aa = 0; aa < FF; aa++) begin : gen_hh
       for (genvar bb = 0; bb < FF; bb++) begin : gen_ii
          if (`asdf [aa]) begin : gen_jj
             assign a[aa][bb] = aa + bb;
             assign b[aa][bb] = aa + bb;
          end : gen_jj
       end : gen_ii
    end : gen_hh


    // this works now with gen/endgen
    generate
       for (genvar aa = 0; aa < FF; aa++) begin : gen_hh
          for (genvar bb = 0; bb < FF; bb++) begin : gen_ii
             always @ (negedge cc)
               a = 5;
             always @ (negedge dd)
               w = 2;
          end : gen_ii
       end : gen_hh
    endgenerate


    // CASE 1 again. No change but works - apparently since verilog-mode hit a generate statement above this line
    for (genvar aa = 0; aa < FF; aa++) begin : gen_hh
       for (genvar bb = 0; bb < FF; bb++) begin : gen_ii
          if (`asdf [aa]) begin : gen_jj

             always_ff @ (negedge cc [aa][bb]) begin
                if (dd [aa][bb])) begin
                   for (uint_t d_idx = 0; d_idx < 16; d_idx++)
                     ee [aa][bb].push_front (tx_dfe_out [aa][bb]  [15 - d_idx]);
                end
             end

             always_ff @ (posedge hs_clk) begin
                ee_size [aa][bb] = ee [aa][bb].size();
                if (ee_size [aa][bb] > 0)
                  gg [aa][bb] <= ee [aa][bb].pop_front;
             end

          end : gen_jj
       end : gen_ii
    end : gen_hh

endmodule : indent
