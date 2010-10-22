module mod1(input logic [1:0] reg1[4],
            input logic       reg2[5][6],
            input logic [1:0] [3:0] [2:0] reg4);
endmodule

module mod2(output logic [1:0] reg1[4],
	    output logic [1:0] [3:0] [2:0] reg4);
endmodule

module dut (
	    /*AUTOINPUT*/
            /*AUTOOUTPUT*/
            );

   /*AUTOWIRE*/

   mod1 foo_i(/*AUTOINST*/);

   /* drv_i AUTO_TEMPLATE (.reg1(reg1[]), );*/
   mod2 drv_i(/*AUTOINST*/);
endmodule
