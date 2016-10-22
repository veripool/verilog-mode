module x (/*AUTOARG*/
   // Inputs
   MIERHW, MBOOTH_P, CEIopMADH_E_D2_R, CEIopMAZH_E_D2_R, DDATAH, DIV2HI, HI_R, MCLA, MCLASH,
   MULTSHCYC, MULTUSCYC, HI_P
   );

   input [18:0] MIERHW;
   integer 	i;
   integer 	MTEMP1;
   integer 	MTEMP2;
   input 	MBOOTH_P;
   input 	CEIopMADH_E_D2_R;
   input 	CEIopMAZH_E_D2_R;
   input 	DDATAH;
   input 	DIV2HI;
   input 	HI_R;
   input 	MCLA;
   input 	MCLASH;
   input 	MULTSHCYC;
   input 	MULTUSCYC;
   input 	HI_P;

   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   // End of automatics

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   // End of automatics

   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   // End of automatics

   always @(/*AUTOSENSE*/MIERHW) begin

      for (i=0; i<=5; i=i+1) begin

	 MTEMP1[3:0] = {MIERHW[i*3+3],
			MIERHW[i*3+2],
			MIERHW[i*3+1],
			MIERHW[i*3+0]};

	 casex (MTEMP1)

           4'b0000: MTEMP2 = 4'b0101; // +0
           4'b0001: MTEMP2 = 4'b0001; // +1
           4'b0010: MTEMP2 = 4'b0001; // +1
           4'b0011: MTEMP2 = 4'b0010; // +2
           4'b0100: MTEMP2 = 4'b0010; // +2
           4'b0101: MTEMP2 = 4'b0100; // +3
           4'b0110: MTEMP2 = 4'b0100; // +3
           4'b0111: MTEMP2 = 4'b1000; // +4
           4'b1000: MTEMP2 = 4'b0111; // -4
           4'b1001: MTEMP2 = 4'b1011; // -3
           4'b1010: MTEMP2 = 4'b1011; // -3
           4'b1011: MTEMP2 = 4'b1101; // -2
           4'b1100: MTEMP2 = 4'b1101; // -2
           4'b1101: MTEMP2 = 4'b1110; // -1
           4'b1110: MTEMP2 = 4'b1110; // -1
           4'b1111: MTEMP2 = 4'b1010; // -0

	 endcase

      end

      {MBOOTH_P[i*4+3],
       MBOOTH_P[i*4+2],
       MBOOTH_P[i*4+1],
       MBOOTH_P[i*4+0]}     = MTEMP2[3:0];

   end

   //  always @(/*AUTOnotSENSE*/
   //           __CEIopMADH_E_D2_R or __CEIopMAZH_E_D2_R or __DIV2HI or
   //           __MULTUSCYC or __MULTSHCYC or
   //           __DDATAH or __HI_R or __MCLA or __MCLASH)  begin

   //  always @(/*AUTOSENSE*/DDATAH or HI_R or MCLA or MCLASH)  begin
`define DMCLASH MCLASH
`define DCONST 1'b1
   always @(/*AUTOSENSE*/CEIopMADH_E_D2_R or CEIopMAZH_E_D2_R or DDATAH or DIV2HI or MCLA or MCLASH
	    or MULTSHCYC or MULTUSCYC)  begin

      case (1'b1)
	CEIopMADH_E_D2_R: HI_P = MCLA;
	CEIopMAZH_E_D2_R: HI_P = MCLA;
	DIV2HI:           HI_P = DDATAH;
	MULTUSCYC:        HI_P = MCLA;
	MULTSHCYC:        HI_P = `DMCLASH;
	default:          HI_P = `DCONST;
      endcase
   end
endmodule

// Local Variables:
// verilog-auto-read-includes:t
// End:
