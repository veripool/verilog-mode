// Issue #1884

module top
(

  (* period=5.0 *)
  input logic clk,

  (* asynchronous=true *)
  input logic rst_n,

  (* attribute1="hello" *)
  /*AUTOINPUT("^a_")*/
  /*AUTOOUTPUT("^a_")*/

  /*AUTOINPUT("^z_")*/
  /*AUTOOUTPUT("^z_")*/

  /*AUTOOUTPUT*/
);

  /*AUTOLOGIC*/

  module_a i_module_a
    (/*AUTOINST*/);

  module_b i_module_b
    (/*AUTOINST*/);

endmodule

module module_a
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic [7:0]  a_data,
  input  logic        a_valid,
  output logic        a_ready,

  output logic [7:0]  b_data,
  output logic        b_valid,
  input  logic        b_ready
);
endmodule

module module_b
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic [7:0]  b_data,
  input  logic        b_valid,
  output logic        b_ready,

  output logic [7:0]  z_data,
  output logic        z_valid,
  input  logic        z_ready
);
endmodule
