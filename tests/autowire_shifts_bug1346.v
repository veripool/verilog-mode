// verilog mode bug1346 testcase
module design(/*AUTOARG*/);
   parameter w1 = 2;
   parameter w2 = 4;
   parameter w3 = 256;
   input [w1:0]       i0;
   input [w2:0]       i1;

   output [w2*w1  :0] y10; // 8:0
   output [w2/w1  :0] y11; // 2:0
   output [w2+w1  :0] y12; // 6:0
   output [w2-w1  :0] y13; // 2:0
   output [w2>>w1 :0] y14; // 1:0
   output [w2>>>w1:0] y15; // 1:0
   output [w2<<w1 :0] y16; //16:0
   output [w2<<<w1:0] y17; //16:0
   output [w2<>>w1:0] y18; //4<>>2:0
   output [w2>><w1:0] y19; //4>><2:0

   output [w1*w2/w1+w1            :0] y20; // 6:0
   output [w2*w1/w1+w1            :0] y21; // 6:0
   output [w1*w2/(w2-w1)+w1       :0] y22; // 6:0
   output [w2*w1/(w2-w1)+w2-w1    :0] y23; // 6:0
   output [w2*w1/(w2-w1)+w1<<1>>1 :0] y24; // 6:0
   output [w2*w1/(w2-w1)+w1<<w1-w1:0] y25; // 6:0
   output [(8*4)-1                :0] y26; // 31:0
   output [((w3>>3)-1)            :0] y27; // 31:0

   output [w2*w1/w1      +w2+w1 <<w2    >>w1   :0] y30; // 40:0
   output [w2*w1/w1      +w1+w2 <<w1+w1 >>w2-w1:0] y31; // 40:0
   output [w2*w1/w1      +w1+w2 <<w1+w1 >>w2/w1:0] y32; // 40:0
   output [w1*w2/w1      +w1+w2 <<w2    >>w1   :0] y33; // 40:0
   output [w1*w2/(w2-w1) +w1+w2 <<w2    >>w1   :0] y34; // 40:0
   output [w1*w2/(w2/w1) +w1+w2 <<w2    >>w2-w1:0] y35; // 40:0
   output [w1*w2/(w1+0)  +w1+w2 <<w2    >>w1   :0] y36; // 40:0

   output [w2*w1/w1      +w2*1+w1 <<w2/1   *1 >>w1   *1:0] y40; // 40:0
   output [w2*w1/w1      +w1*1+w2 <<w1/1+w1*1 >>w2-w1*1:0] y41; // 40:0
   output [w2*w1/w1      +w1*1+w2 <<w1/1+w1*1 >>w2/w1*1:0] y42; // 40:0
   output [w1*w2/w1      +w1*1+w2 <<w2/1   *1 >>w1   *1:0] y43; // 40:0
   output [w1*w2/(w2-w1) +w1*1+w2 <<w2/1   *1 >>w1   *1:0] y44; // 40:0
   output [w1*w2/(w2/w1) +w1*1+w2 <<w2/1   *1 >>w2-w1*1:0] y45; // 40:0
endmodule // design

module test(/*AUTOARG*/);

   /*AUTOINPUT*/

   /*AUTOOUTPUT*/

   design #(.w1(2),.w2(4),.w3(256)) i0_design(/*AUTOINST*/);

endmodule // test

// Local Variables:
// verilog-auto-inst-param-value: t
// End:
