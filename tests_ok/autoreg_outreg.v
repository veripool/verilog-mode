module foo
  #(parameter
    PARAM3_P=99)
   (
    output                     sig3,// Here, I've hit "tab" twice and this line is correct
    output reg [PARAM2_P-1:0]  s4, // Comment here which should be at "comment-column"
    output wire [PARAM2_P-1:0] sig5,// Comment here which should be at "comment-column"
    input                      reset_L// module reset: global register
    );
   
   /*AUTOWIRE*/
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [PARAM2_P-1:0] s4;
   reg                sig3;
   reg [PARAM2_P-1:0] sig5;
   // End of automatics
   
endmodule
