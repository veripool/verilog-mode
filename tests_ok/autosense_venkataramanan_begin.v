
module autosense_venkataramanan_begin(/*AUTOARG*/);
   
   reg a,b;
   
   always @(/*AUTOSENSE*/b) // I didn't expect to get "i" in AUTOSENSE
     begin : label
        integer       i, j;
        for (i=0; i< = 3; i = i + 1)
          vec[i] = b;
     end
   
endmodule

// Local Variables:
// verilog-auto-sense-defines-constant: t
// verilog-auto-sense-include-inputs: t
// End:
