// Ignore indentation for outshine header lines that start with // *

// * Header1
   // * Header2
      // * Header3
         // ** SubHeader3


// * Header1
   // * Header2
// * Header3
          // ** SubHeader3

                             // * Header1
        // * Header2
                                                   // * Header3
             // ** SubHeader3


// Some example module to check that the rest of indentation works fine
module ram_controller ();

ram_sp_sr_sw #(
.DATA_WIDTH(16),
.ADDR_WIDTH(8),
.RAM_DEPTH(256)
) ram (
clk,
address,
data,
cs,
we,
oe
)
;

endmodule


// Local Variables:
// verilog-indent-ignore-regexp: "// \\*"
// End:
