
module autowire_req ();

reqcmd_t AReq;
reqcmd_t BReq;

/*AUTOWIRE*/

autowire_req_sw  autowire_req_sw (/*AUTOINST*/
				  // Outputs
				  .BReq			(BReq),
				  // Inputs
				  .AReq			(AReq));

endmodule

// Local Variables:
// verilog-library-directories:(".")
// verilog-typedef-regexp:"_t$"
// End:
