module autoinst_ams_vorwerk;

  latch latch (/*AUTOINST*/);

endmodule

module latch (/*AUTOARG*/);

`ifdef __VAMS_ENABLE__
    output (* integer groundSensitivity="gnd "; integer supplySensitivity="vdd "; *) q;
 `else
    output q;
`endif

`ifdef __VAMS_ENABLE__
    input (* integer groundSensitivity="gnd "; integer supplySensitivity="vdd "; *) en;
 `else
    input en;
`endif

`ifdef __VAMS_ENABLE__
    input (* integer groundSensitivity="gnd "; integer supplySensitivity="vdd "; *) d;
 `else
    input d;
`endif

endmodule
