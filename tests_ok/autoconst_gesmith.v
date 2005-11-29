module(/*AUTOARG*/)


  always @(`ot.BOZ or
	   /*AUTOSENSE*/b)
    begin
       /*AUTO_CONSTANT(`ot.BOC) */
       i = b;
       c = `ot.BOC;
       d = `ot.BOZ;
    end

   always @(/*AUTOSENSE*/b)
     begin
	/*AUTO_CONSTANT(ot.BOB) */
	i = b;
	c = ot.BOB;
     end

endmodule
