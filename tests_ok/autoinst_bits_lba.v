module lba
  
  (/*AUTOnotARG*/
   // Outputs
   );
   
   
   /* autoinst_bits_lba_gi      AUTO_TEMPLATE   (
    .WWCmdI     (WWCmdI[]));
    */
   
   autoinst_bits_lba_gi gi      (/*AUTOINST*/
                                 // Outputs
                                 .WWCmdI                (WWCmdI[8:0]),   // Templated
                                 .WWADI                 (WWADI[31:0]),
                                 // Inouts
                                 .WWADB                 (WWADB[31:0]),
                                 .WWCmdB                (WWCmdB[8:0]),
                                 // Inputs
                                 .CLK                   (CLK),
                                 .WWADoe                (WWADoe),
                                 .WWCoe                 (WWCoe),
                                 .WWCmdIfOE             (WWCmdIfOE[8:0]),
                                 .WWADHold              (WWADHold),
                                 .iWWADO                (iWWADO[31:0]));
   
endmodule
