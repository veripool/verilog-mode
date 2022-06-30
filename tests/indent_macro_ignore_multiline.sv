// Issue 1082

`define drive_agt(AGT_ID) \
  begin \
      some_agt_seq seq; \
      seq = some_agt_seq::type_id::create \
                 (.name({"some_agt_seq_",$sformatf("%0d", AGT_ID)}), \
                  .contxt(get_full_name())); \
      seq.start(env.adc_agt[AGT_ID].sqr_l1); \
  end


  `define foo(ARG) \
     begin \
       $display(\"Bar\"); \
       $display(\"Baz\"); \
     end


`define foo(ARG) \
     begin \
         $display(\"Bar\"); \
         $display(\"Baz\"); \
     end


// Indentation should also ignore multiline macros with trailing whitespaces
`define foo(ARG) \       
     begin \    
         $display(\"Bar\"); \       
         $display(\"Baz\"); \  
     end



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
// verilog-indent-ignore-multiline-defines: t
// End:
