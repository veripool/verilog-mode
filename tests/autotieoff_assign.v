module autotieoff_signed (/*AUTOARG*/);
   
   output [2:0]        ExtraOut;
   output [2:0]        SubOut;
   output [3:0]        active_low_l;
   output [3:0]        ignored_by_regexp;
   
   /*AUTOTIEOFF*/
   
endmodule

module sub;
   input  SubIn;
   output SubOut;
endmodule

// Local Variables:
// verilog-auto-tieoff-declaration: "assign"
// End:
