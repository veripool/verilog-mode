module foobar;
   
   sequence s_1;
      {txd, txdk} && (ppd == 3'b000) && !txe;
   endsequence // s_1
  
   sequence s_phy_transmitting;
      {rxd, rxdk} && 
	((ppd == 3'b000) || (ppd == 3'b001))
	&& rxv;
   endsequence // s_phy_transmitting
   
  
endmodule
