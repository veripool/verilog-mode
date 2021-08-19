
//bug1061

//typedef logic [7:0] foo_t;
module ptype
  (
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input              foo_t a, // To b0 of ptype_buf.v, ...
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output             foo_t y0, // From b0 of ptype_buf.v
   output logic [7:0] y1, // From b1 of ptype_buf.v
   output             TYPE_T y2                 // From b2 of ptype_buf.v
   // End of automatics
   );
   
   ptype_buf #(.TYPE_T(foo_t)) b0
     (// Outputs
      .y                                (y0),
      /*AUTOINST*/
      // Inputs
      .a                                (a));
   
   ptype_buf #(.TYPE_T(logic [7:0])) b1
     (// Outputs
      .y                                (y1),
      /*AUTOINST*/
      // Inputs
      .a                                (a));
   
   ptype_buf #(.WIDTH(8)) b2
     (// Outputs
      .y                                (y2),
      /*AUTOINST*/
      // Inputs
      .a                                (a));
   
endmodule

module ptype_buf
  #(parameter WIDTH = 1,
    parameter type TYPE_T = logic [WIDTH-1:0])
   (output TYPE_T y,
    input TYPE_T a);
   assign y = a;
endmodule

///--------------

// Example in docs

module InstModule (o,i);
   parameter         WIDTH;
   input [WIDTH-1:0] i;
   parameter         type OUT_t;
   output            OUT_t o;
endmodule

module ExampInst;
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [9:0] i; // To instName of InstModule.v
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output      upper_t o;                          // From instName of InstModule.v
   // End of automatics
   
   InstModule
     #(.WIDTH(10),
       ,.OUT_t(upper_t))
   instName
     (/*AUTOINST*/
      // Outputs
      .o                        (o),
      // Inputs
      .i                        (i[9:0]));
endmodule

// Local Variables:
// verilog-typedef-regexp: "_[tT]$"
// verilog-auto-inst-param-value:t
// verilog-auto-inst-param-value-type:t
// End:
