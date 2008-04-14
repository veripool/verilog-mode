typedef logic [3:0][1:0] sometype_t;

module top
  #(parameter X=4,
    parameter Y=1)

   (input clk,
    input rstb,

    /*AUTOINPUT("^x.*\|v.*")*/
    /*AUTOOUTPUT("^c.*\|k.*")*/

    /*AUTOOUTPUT("^y.*")*/

    /*AUTOINPUT*/
    /*AUTOOUTPUT*/
    // Beginning of automatic outputs (from unused autoinst outputs)
    output		foobar,			// From XX of xx.v
    output [4:0] [2:0]	foobar2		// From YY of yy.v
    // End of automatics
    );

   xx (/*AUTOINSTPARAM*/
       // Parameters
       .X				(X),
       .Y				(Y))
     XX(/*AUTOINST*/
	// Outputs
	.st				(st[1:0]),
	.foobar				(foobar),
	// Inputs
	.clk				(clk),
	.rstb				(rstb),
	.xc				(xc/*[X-1:0][1:0]*/),
	.xa				(xa[X-1:0]),
	.xb				(xb[X-1:0]),
	.cb				(cb[X-1:0]),
	.yb				(yb[X*Y-1:0]));
   
   yy (/*AUTOINSTPARAM*/
       // Parameters
       .X				(X),
       .Y				(Y))
     YY(/*AUTOINST*/
	// Outputs
	.xc				(xc/*[X-1:0][1:0]*/),
	.xa				(xa[X-1:0]),
	.yb				(yb[X*Y-1:0]),
	.foobar2			(foobar2/*[4:0][2:0]*/),
	// Inputs
	.clk				(clk),
	.rstb				(rstb),
	.xb				(xb[X-1:0]),
	.cb				(cb[X-1:0]),
	.st				(st[1:0]));

endmodule // top

module xx
  #(parameter X=4,
    parameter Y=1)
   (input clk,
    input rstb,

    input [X-1:0][1:0] xc,
    input [X-1:0] xa,
    input [X-1:0] xb,

    input [X-1:0] cb,
    output sometype_t [1:0]  st,

    input [X*Y-1:0] yb,

    output foobar
    );

endmodule // xx

module yy
  #(parameter X=4,
    parameter Y=1)
   (input clk,
    input rstb,

    output [X-1:0][1:0] xc,
    output [X-1:0] xa,
    input [X-1:0] xb,

    input [X-1:0] cb,
    input         sometype_t [1:0] st,

    output [X*Y-1:0] yb,

    output [4:0][2:0] foobar2
    );

endmodule // xx

// Local Variables:
// verilog-typedef-regexp:"_t$"
// verilog-library-directories:("." )
// verilog-library-extensions:(".v" ".sv" ".h" ".vr" ".vm")
// End:
