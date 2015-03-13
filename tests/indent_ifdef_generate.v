// Issue 559 - nested ifdef with generate indentation bug
module m;

`ifndef DDR_PT_GATE_SIM
generate
/***************** Assertions for DP HM signals ***************************************************************/
for (dp_id=0; dp_id <PDDR_NUM_DP; dp_id++) begin: DPConnectGen

if (PDDR_DP_HV[dp_id]) begin: VGen
`ifdef IO_DDR3
// CR?V connectivity for DP HM
DP_CRN0V15_Connection: assert property (ConnectProp(1'b1, `PHYTOP.CRN0V[dp_id+PGEN_NUM_ADR], `PHYTOP.DPBundleGen[dp_id].u_DpBundle.`DPV_INST.CRN0V15))
else begin
$display ($stime, " ERROR: CRN0V[%0d] to DP HM %0d CRN0V15 Connection Failed", dp_id+PGEN_NUM_ADR, dp_id);

postError();

end // else: !assert property
DP_CRN1V15_Connection: assert property (ConnectProp(1'b1, `PHYTOP.CRN1V[dp_id+PGEN_NUM_ADR], `PHYTOP.DPBundleGen[dp_id].u_DpBundle.`DPV_INST.CRN1V15))
else begin
$display ($stime, " ERROR: CRN1V[%0d] to DP HM %0d CRN1V15 Connection Failed", dp_id+PGEN_NUM_ADR, dp_id);

postError();

end // else: !assert property
end // block: VGen
`endif //  `ifdef IO_DDR3
end // block: DPConnectGen
endgenerate
`endif

endmodule // m
