// Bug 636
module mymodule (input logic  reset_n,
                  input logic  clock,
                               streambus.sink sink,
                               streambus.source source,
                  output logic interrupt_pulse);

    logic [31:0]               test;
    streambus.source source;
endmodule
