module foo;
   input a;
   input b;
   input [1:0] cfg_dev_i; // Config Device: 0b00 = Pangu, 0b01 = Switch
   output switch_idsel_o; // Switch PCI IDSEL
   output pangu_idsel_o;                    // Pangu PCI IDSEL
   output wire g;
   inout wire  h;
endmodule // foo
