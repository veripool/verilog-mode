// See bug320

interface intf1;
  logic a;
  logic b;
  modport mp1 (input a, output b);
endinterface

interface intf2 (intf1.mp1 c);
  logic e;
endinterface

module top;
  intf1 c(.*);
  intf2 f(.*);
endmodule
