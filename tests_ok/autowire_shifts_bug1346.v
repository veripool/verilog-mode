// verilog mode bug1346 testcase
module design(/*AUTOARG*/
              // Outputs
              y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y30,
              y31, y32, y33, y34, y35, y36, y40, y41, y42, y43, y44, y45,
              // Inputs
              i0, i1
              );
   parameter                                             w1 = 2;
   parameter                                             w2 = 4;
   parameter                                             w3 = 256;
   input [w1:0]                                          i0;
   input [w2:0]                                          i1;
   
   output [w2*w1 :0]                                     y10; // 8:0
   output [w2/w1 :0]                                     y11; // 2:0
   output [w2+w1 :0]                                     y12; // 6:0
   output [w2-w1 :0]                                     y13; // 2:0
   output [w2>>w1 :0]                                    y14; // 1:0
   output [w2>>>w1:0]                                    y15; // 1:0
   output [w2<<w1 :0]                                    y16; //16:0
   output [w2<<<w1:0]                                    y17; //16:0
   output [w2<>>w1:0]                                    y18; //4<>>2:0
   output [w2>><w1:0]                                    y19; //4>><2:0
   
   output [w1*w2/w1+w1 :0]                               y20; // 6:0
   output [w2*w1/w1+w1 :0]                               y21; // 6:0
   output [w1*w2/(w2-w1)+w1 :0]                          y22; // 6:0
   output [w2*w1/(w2-w1)+w2-w1 :0]                       y23; // 6:0
   output [w2*w1/(w2-w1)+w1<<1>>1 :0]                    y24; // 6:0
   output [w2*w1/(w2-w1)+w1<<w1-w1:0]                    y25; // 6:0
   output [(8*4)-1 :0]                                   y26; // 31:0
   output [((w3>>3)-1) :0]                               y27; // 31:0
   
   output [w2*w1/w1 +w2+w1 <<w2 >>w1 :0]                 y30; // 40:0
   output [w2*w1/w1 +w1+w2 <<w1+w1 >>w2-w1:0]            y31; // 40:0
   output [w2*w1/w1 +w1+w2 <<w1+w1 >>w2/w1:0]            y32; // 40:0
   output [w1*w2/w1 +w1+w2 <<w2 >>w1 :0]                 y33; // 40:0
   output [w1*w2/(w2-w1) +w1+w2 <<w2 >>w1 :0]            y34; // 40:0
   output [w1*w2/(w2/w1) +w1+w2 <<w2 >>w2-w1:0]          y35; // 40:0
   output [w1*w2/(w1+0) +w1+w2 <<w2 >>w1 :0]             y36; // 40:0
   
   output [w2*w1/w1 +w2*1+w1 <<w2/1 *1 >>w1 *1:0]        y40; // 40:0
   output [w2*w1/w1 +w1*1+w2 <<w1/1+w1*1 >>w2-w1*1:0]    y41; // 40:0
   output [w2*w1/w1 +w1*1+w2 <<w1/1+w1*1 >>w2/w1*1:0]    y42; // 40:0
   output [w1*w2/w1 +w1*1+w2 <<w2/1 *1 >>w1 *1:0]        y43; // 40:0
   output [w1*w2/(w2-w1) +w1*1+w2 <<w2/1 *1 >>w1 *1:0]   y44; // 40:0
   output [w1*w2/(w2/w1) +w1*1+w2 <<w2/1 *1 >>w2-w1*1:0] y45; // 40:0
endmodule // design

module test(/*AUTOARG*/
            // Outputs
            y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y30,
            y31, y32, y33, y34, y35, y36, y40, y41, y42, y43, y44, y45,
            // Inputs
            i0, i1
            );
   
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [2:0]      i0; // To i0_design of design.v
   input [4:0]      i1; // To i0_design of design.v
   // End of automatics
   
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [8:0]     y10; // From i0_design of design.v
   output [2:0]     y11; // From i0_design of design.v
   output [6:0]     y12; // From i0_design of design.v
   output [2:0]     y13; // From i0_design of design.v
   output [1:0]     y14; // From i0_design of design.v
   output [1:0]     y15; // From i0_design of design.v
   output [16:0]    y16; // From i0_design of design.v
   output [16:0]    y17; // From i0_design of design.v
   output [4<>>2:0] y18; // From i0_design of design.v
   output [4>><2:0] y19; // From i0_design of design.v
   output [6:0]     y20; // From i0_design of design.v
   output [6:0]     y21; // From i0_design of design.v
   output [6:0]     y22; // From i0_design of design.v
   output [6:0]     y23; // From i0_design of design.v
   output [6:0]     y24; // From i0_design of design.v
   output [6:0]     y25; // From i0_design of design.v
   output [31:0]    y26; // From i0_design of design.v
   output [31:0]    y27; // From i0_design of design.v
   output [40:0]    y30; // From i0_design of design.v
   output [40:0]    y31; // From i0_design of design.v
   output [40:0]    y32; // From i0_design of design.v
   output [40:0]    y33; // From i0_design of design.v
   output [40:0]    y34; // From i0_design of design.v
   output [40:0]    y35; // From i0_design of design.v
   output [40:0]    y36; // From i0_design of design.v
   output [40:0]    y40; // From i0_design of design.v
   output [40:0]    y41; // From i0_design of design.v
   output [40:0]    y42; // From i0_design of design.v
   output [40:0]    y43; // From i0_design of design.v
   output [40:0]    y44; // From i0_design of design.v
   output [40:0]    y45;                        // From i0_design of design.v
   // End of automatics
   
   design #(.w1(2),.w2(4),.w3(256)) i0_design(/*AUTOINST*/
                                              // Outputs
                                              .y10              (y10[8:0]),
                                              .y11              (y11[2:0]),
                                              .y12              (y12[6:0]),
                                              .y13              (y13[2:0]),
                                              .y14              (y14[1:0]),
                                              .y15              (y15[1:0]),
                                              .y16              (y16[16:0]),
                                              .y17              (y17[16:0]),
                                              .y18              (y18[4<>>2:0]),
                                              .y19              (y19[4>><2:0]),
                                              .y20              (y20[6:0]),
                                              .y21              (y21[6:0]),
                                              .y22              (y22[6:0]),
                                              .y23              (y23[6:0]),
                                              .y24              (y24[6:0]),
                                              .y25              (y25[6:0]),
                                              .y26              (y26[31:0]),
                                              .y27              (y27[31:0]),
                                              .y30              (y30[40:0]),
                                              .y31              (y31[40:0]),
                                              .y32              (y32[40:0]),
                                              .y33              (y33[40:0]),
                                              .y34              (y34[40:0]),
                                              .y35              (y35[40:0]),
                                              .y36              (y36[40:0]),
                                              .y40              (y40[40:0]),
                                              .y41              (y41[40:0]),
                                              .y42              (y42[40:0]),
                                              .y43              (y43[40:0]),
                                              .y44              (y44[40:0]),
                                              .y45              (y45[40:0]),
                                              // Inputs
                                              .i0               (i0[2:0]),
                                              .i1               (i1[4:0]));
   
endmodule // test

// Local Variables:
// verilog-auto-inst-param-value: t
// End:
