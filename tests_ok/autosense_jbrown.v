`define LCH_GSWDATWID  3
`define COM_CLDATWID   2

module autosense_jbrown(/*AUTOARG*/
   // Outputs
   lch_gswdata,
   // Inputs
   com_cldata
   );

   output [`LCH_GSWDATWID-1:0]    lch_gswdata;    // data to switch
   input [`COM_CLDATWID-1:0] 	  com_cldata;     // data bus to clusters

   /*autowire*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics

   reg 				  tmp;
`define TEST_DEFINE   1'b0
   always @ (/*AUTOSENSE*/)
     begin
        /* AUTO_CONSTANT (`TEST_DEFINE) */
        tmp <= `TEST_DEFINE;  // test defines
     end

   // Local Variables:
   // verilog-library-directories:("." "../cdp/")
   // verilog-library-extensions:(".v" ".vh")
   // End:

endmodule
