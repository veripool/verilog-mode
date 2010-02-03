typedef node logic;

module top
  #(parameter COLS = 4
    )
  ( input logic clk,
    input logic rstb,
    input logic [COLS-1:0] ival,
    input logic [COLS-1:0][1:0] idata_some_extra_sig_length,

    input logic [COLS-1:0][7:0] isig1,
    input logic [COLS-1:0][6:0] isig2,
    input logic [COLS-1:0][5:0] isig3,
    /*AUTOINPUT*/
    // Beginning of automatic inputs (from unused autoinst inputs)
    input		idata_some_extra_sig_lengt,// To isub1 of sub1.v, ...
    input		isig,			// To isub1 of sub1.v, ...
    // End of automatics

    output logic [COLS-1:0] oval,
    output logic [COLS-1:0][1:0] odata,
    output logic [COLS-1:0] s3_oval,
    output logic [COLS-1:0][1:0] s3_odata,

    /*AUTOOUTPUT*/
    // Beginning of automatic outputs (from unused autoinst outputs)
    output		s1_odat,		// From isub1 of sub1.v
    output		s3_odat		// From isub3 of sub3.v
    // End of automatics
    );


   logic [COLS-1:0][1:0]           s1_odata;               // From isub1 of sub1.v
   logic [COLS-1:0]           s1_oval;                // From isub1 of sub1.v
   /*AUTOWIRE*/
   
   /* sub2 AUTO_TEMPLATE(
    .idata_some_extra_sig_length ( s1_odata),
    .ival ( s1_oval),
    );*/
   sub2 isub2 (/*AUTOINST*/
	       // Outputs
	       .oval			(oval[COLS-1:0]),
	       .odata			(odata/*[COLS-1:0][1:0]*/),
	       // Inputs
	       .clk			(clk),
	       .rstb			(rstb),
	       .ival			( s1_oval),		 // Templated
	       .idata_some_extra_sig_length( s1_odata));		 // Templated

   genvar column;
   /* sub1 AUTO_TEMPLATE(
    .i.* ( @"vl-name"[column] @"(if (or(>(length vl-mbits)0) (>(length vl-bits)0)) (concat \\"/\\* \\" vl-mbits vl-bits \\" *\\/\\") )"),
    .o.* ( s1_@"vl-name"[column] @"(if (or(>(length vl-mbits)0) (>(length vl-bits)0)) (concat \\"/\\* \\" vl-mbits vl-bits \\" *\\/\\") )"),
    );*/
   /* sub3 AUTO_TEMPLATE(
    .i.* ( @"vl-name"[column] @"(if (or(>(length vl-mbits)0) (>(length vl-bits)0)) (concat \\"/\\* \\" vl-mbits vl-bits \\" *\\/\\") )"),
    .o.* ( s3_@"vl-name"[column] @"(if (or(>(length vl-mbits)0) (>(length vl-bits)0)) (concat \\"/\\* \\" vl-mbits vl-bits \\" *\\/\\") )"),
    );*/
   generate for(column=0;column<4;column++) begin : COLUMN
      sub1 isub1(/*AUTOINST*/
		 // Outputs
		 .oval			( s1_oval[column] ),	 // Templated
		 .odata			( s1_odata[column] /* [1:0] */), // Templated
		 // Inputs
		 .clk			(clk),
		 .rstb			(rstb),
		 .ival			( ival[column] ),	 // Templated
		 .idata_some_extra_sig_length( idata_some_extra_sig_length[column] /* [1:0] */), // Templated
		 .isig1			( isig1[column] /* [7:0] */), // Templated
		 .isig2			( isig2[column] /* [6:0] */), // Templated
		 .isig3			( isig3[column] /* [5:0] */)); // Templated
      sub3 isub3(/*AUTOINST*/
		 // Outputs
		 .oval			( s3_oval[column] ),	 // Templated
		 .odata			( s3_odata[column] /* [1:0] */), // Templated
		 // Inputs
		 .clk			(clk),
		 .rstb			(rstb),
		 .ival			( ival[column] ),	 // Templated
		 .idata_some_extra_sig_length( idata_some_extra_sig_length[column] /* [1:0] */)); // Templated
      
   end endgenerate

   
endmodule // top

module sub1
  ( input logic clk,
    input logic rstb,
    input logic ival,
    input logic [1:0] idata_some_extra_sig_length,
    input logic [7:0] isig1,
    input logic [6:0] isig2,
    input logic [5:0] isig3,
    output logic oval,
    output logic [1:0] odata
    );
endmodule // sub
module sub3
  ( input logic clk,
    input logic rstb,
    input logic ival,
    input logic [1:0] idata_some_extra_sig_length,
    output logic oval,
    output logic [1:0] odata
    );
endmodule // sub

module sub2
  #(parameter COLS = 4
    )
  ( input logic clk,
    input logic rstb,
    input logic [COLS-1:0] ival,
    input logic [COLS-1:0][1:0] idata_some_extra_sig_length,
    output logic [COLS-1:0] oval,
    output logic [COLS-1:0] [1:0] odata
    );
endmodule // sub
// Local Variables:
// verilog-typedef-regexp:"\\(^t_\\)\\|\\(^node$\\)\\|\\(_s$\\)\\|\\(_t$\\)"
// verilog-library-directories:("." )
// verilog-library-extensions:(".v" ".sv" ".h" ".vr" ".vm")
// End:
