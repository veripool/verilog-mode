// See http://www.veripool.org/issues/show/270

interface autoinst_iface270_sub;
   logic a;
   logic b;
   modport master_mp(input a, output b);
   modport slave_mp(output a, input b);
   modport monitor (input a, input b);
endinterface
