// bug861/862 - named coverpoint inside/near pre-processor macro confuses indentation
module m;

`ifdef ASSERT_ON
asrt_001: assert property(p_001);
asrt_002: assert property(p_002);
asrt_003: assert property(p_003);
`endif

`ifdef COVER_ON
chk_001: cover property(p_001);
chk_002: cover property(p_002);
chk_003: cover property(p_003);
`endif

endmodule
