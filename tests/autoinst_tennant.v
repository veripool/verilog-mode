typedef logic [3:0][1:0] sometype_t;

module top
  #(parameter X=4,
    parameter Y=1)

   (input clk,
    input rstb,

    /*AUTOINPUT("^x.\|v.**")*/
    /*AUTOOUTPUT("^c.*\|k.*")*/

    /*AUTOOUTPUT("^y.*")*/

    /*AUTOINPUT*/
    /*AUTOOUTPUT*/
    );

   xx (/*AUTOINSTPARAM*/)
     XX(/*AUTOINST*/);
   
   yy (/*AUTOINSTPARAM*/)
     YY(/*AUTOINST*/);

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
